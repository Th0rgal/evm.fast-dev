import InitECandidate.Proofs.WordStages.Source510
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody526_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody526_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody526_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([10, 28, 6, 24]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody526_0, 526, 2)) (some 471) ([]) (some (16, sourceBody526_1, 526, 3))

def sourceBody526_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody526_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody526_2 sourceBody526_3

def sourceBody526_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody526_4 sourceBody526_0

def sourceBody526_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody526_7 : WordLangProgHOL (BitVec 64) :=
.call (some (([16, 34, 4, 22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody526_0, 526, 4)) (some 471) ([]) (some (14, sourceBody526_6, 526, 5))

def sourceBody526_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody526_7 sourceBody526_3

def sourceBody526_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody526_8 sourceBody526_0

def sourceBody526_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.const 3#64)

def sourceBody526_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 10)

def sourceBody526_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 28)

def sourceBody526_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 6)

def sourceBody526_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 24)

def sourceBody526_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody526_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody526_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody526_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody526_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 32

def sourceBody526_20 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody526_0, 526, 6)) (some 479) ([32, 8, 26, 18, 36, 2, 20, 12, 30]) (some (32, sourceBody526_19, 526, 7))

def sourceBody526_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody526_20 sourceBody526_3

def sourceBody526_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody526_21 sourceBody526_0

def sourceBody526_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody526_18 sourceBody526_22

def sourceBody526_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody526_17 sourceBody526_23

def sourceBody526_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody526_16 sourceBody526_24

def sourceBody526_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody526_15 sourceBody526_25

def sourceBody526_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody526_14 sourceBody526_26

def sourceBody526_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody526_13 sourceBody526_27

def sourceBody526_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody526_12 sourceBody526_28

def sourceBody526_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody526_11 sourceBody526_29

def sourceBody526_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody526_10 sourceBody526_30

def sourceBody526_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody526_0 sourceBody526_31

def sourceBody526_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody526_0 sourceBody526_32

def sourceBody526_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 10)

def sourceBody526_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 28)

def sourceBody526_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 6)

def sourceBody526_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 24)

def sourceBody526_38 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody526_0, 526, 8)) (some 458) ([32, 8, 26, 18]) (some (32, sourceBody526_19, 526, 9))

def sourceBody526_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody526_38 sourceBody526_3

def sourceBody526_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody526_39 sourceBody526_0

def sourceBody526_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody526_37 sourceBody526_40

def sourceBody526_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody526_36 sourceBody526_41

def sourceBody526_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody526_35 sourceBody526_42

def sourceBody526_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody526_34 sourceBody526_43

def sourceBody526_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 16)

def sourceBody526_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 34)

def sourceBody526_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 4)

def sourceBody526_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 22)

def sourceBody526_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2
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
      Flapjack.WordLangExpHOL.var 14])

def sourceBody526_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody526_51 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody526_0, 526, 10)) (some 147) ([8, 26, 18, 36, 2]) (some (8, sourceBody526_50, 526, 11))

def sourceBody526_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody526_51 sourceBody526_3

def sourceBody526_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody526_52 sourceBody526_0

def sourceBody526_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody526_49 sourceBody526_53

def sourceBody526_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody526_48 sourceBody526_54

def sourceBody526_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody526_47 sourceBody526_55

def sourceBody526_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody526_46 sourceBody526_56

def sourceBody526_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody526_45 sourceBody526_57

def sourceBody526_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody526_0 sourceBody526_58

def sourceBody526_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody526_0 sourceBody526_59

def sourceBody526_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody526_62 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody526_0, 526, 12)) (some 486) ([8]) (some (8, sourceBody526_50, 526, 13))

def sourceBody526_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody526_62 sourceBody526_3

def sourceBody526_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody526_63 sourceBody526_0

def sourceBody526_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody526_61 sourceBody526_64

def sourceBody526_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody526_0 sourceBody526_65

def sourceBody526_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody526_0 sourceBody526_66

def sourceBody526_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody526_60 sourceBody526_67

def sourceBody526_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody526_70 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [32]

def sourceBody526_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody526_70 sourceBody526_0

def sourceBody526_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody526_69 sourceBody526_71

def sourceBody526_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody526_68 sourceBody526_72

def sourceBody526_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody526_44 sourceBody526_73

def sourceBody526_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody526_0 sourceBody526_74

def sourceBody526_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody526_0 sourceBody526_75

def sourceBody526_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody526_33 sourceBody526_76

def sourceBody526_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody526_9 sourceBody526_77

def sourceBody526_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody526_0 sourceBody526_78

def sourceBody526_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody526_0 sourceBody526_79

def sourceBody526_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody526_0 sourceBody526_80

def sourceBody526_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody526_0 sourceBody526_81

def sourceBody526_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody526_0 sourceBody526_82

def sourceBody526_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody526_0 sourceBody526_83

def sourceBody526_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody526_0 sourceBody526_84

def sourceBody526_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody526_0 sourceBody526_85

def sourceBody526_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody526_5 sourceBody526_86

def sourceBody526_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody526_0 sourceBody526_87

def sourceBody526_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody526_0 sourceBody526_88

def sourceBody526_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody526_0 sourceBody526_89

def sourceBody526_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody526_0 sourceBody526_90

def sourceBody526_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody526_0 sourceBody526_91

def sourceBody526_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody526_0 sourceBody526_92

def sourceBody526_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody526_0 sourceBody526_93

def sourceBody526_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody526_0 sourceBody526_94

def source526 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (526, 1, sourceBody526_95)
end InitECandidate.Proofs.WordStages
