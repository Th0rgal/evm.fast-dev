import InitECandidate.Proofs.WordStages.Source531
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody547_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody547_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody547_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([10, 24, 6, 20]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody547_0, 547, 2)) (some 471) ([]) (some (14, sourceBody547_1, 547, 3))

def sourceBody547_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody547_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody547_2 sourceBody547_3

def sourceBody547_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody547_4 sourceBody547_0

def sourceBody547_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 100#64)

def sourceBody547_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 28

def sourceBody547_8 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody547_0, 547, 4)) (some 466) ([28]) (some (28, sourceBody547_7, 547, 5))

def sourceBody547_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody547_8 sourceBody547_3

def sourceBody547_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody547_9 sourceBody547_0

def sourceBody547_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody547_6 sourceBody547_10

def sourceBody547_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody547_0 sourceBody547_11

def sourceBody547_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody547_0 sourceBody547_12

def sourceBody547_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 280#64]))

def sourceBody547_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 10)

def sourceBody547_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 24)

def sourceBody547_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 6)

def sourceBody547_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 20)

def sourceBody547_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 14)

def sourceBody547_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 4

def sourceBody547_21 : WordLangProgHOL (BitVec 64) :=
.call (some (([28]), ((Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody547_0, 547, 6)) (some 147) ([4, 18, 12, 26, 8]) (some (4, sourceBody547_20, 547, 7))

def sourceBody547_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody547_21 sourceBody547_3

def sourceBody547_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody547_22 sourceBody547_0

def sourceBody547_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody547_19 sourceBody547_23

def sourceBody547_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody547_18 sourceBody547_24

def sourceBody547_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody547_17 sourceBody547_25

def sourceBody547_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody547_16 sourceBody547_26

def sourceBody547_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody547_15 sourceBody547_27

def sourceBody547_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody547_0 sourceBody547_28

def sourceBody547_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody547_0 sourceBody547_29

def sourceBody547_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
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

def sourceBody547_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 28)

def sourceBody547_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 14)

def sourceBody547_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody547_35 : WordLangProgHOL (BitVec 64) :=
.call (some (([4, 18, 12, 26]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody547_0, 547, 8)) (some 408) ([8, 22]) (some (8, sourceBody547_34, 547, 9))

def sourceBody547_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody547_35 sourceBody547_3

def sourceBody547_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody547_36 sourceBody547_0

def sourceBody547_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody547_33 sourceBody547_37

def sourceBody547_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody547_32 sourceBody547_38

def sourceBody547_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 4)

def sourceBody547_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 18)

def sourceBody547_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 12)

def sourceBody547_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 26)

def sourceBody547_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 22

def sourceBody547_45 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody547_0, 547, 10)) (some 472) ([22, 16, 30, 2]) (some (22, sourceBody547_44, 547, 11))

def sourceBody547_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody547_45 sourceBody547_3

def sourceBody547_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody547_46 sourceBody547_0

def sourceBody547_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody547_43 sourceBody547_47

def sourceBody547_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody547_42 sourceBody547_48

def sourceBody547_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody547_41 sourceBody547_49

def sourceBody547_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody547_40 sourceBody547_50

def sourceBody547_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody547_0 sourceBody547_51

def sourceBody547_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody547_0 sourceBody547_52

def sourceBody547_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody547_55 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody547_0, 547, 12)) (some 486) ([22]) (some (22, sourceBody547_44, 547, 13))

def sourceBody547_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody547_55 sourceBody547_3

def sourceBody547_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody547_56 sourceBody547_0

def sourceBody547_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody547_54 sourceBody547_57

def sourceBody547_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody547_0 sourceBody547_58

def sourceBody547_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody547_0 sourceBody547_59

def sourceBody547_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody547_53 sourceBody547_60

def sourceBody547_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody547_63 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [8]

def sourceBody547_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody547_63 sourceBody547_0

def sourceBody547_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody547_62 sourceBody547_64

def sourceBody547_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody547_61 sourceBody547_65

def sourceBody547_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody547_39 sourceBody547_66

def sourceBody547_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody547_0 sourceBody547_67

def sourceBody547_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody547_0 sourceBody547_68

def sourceBody547_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody547_0 sourceBody547_69

def sourceBody547_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody547_0 sourceBody547_70

def sourceBody547_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody547_0 sourceBody547_71

def sourceBody547_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody547_0 sourceBody547_72

def sourceBody547_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody547_0 sourceBody547_73

def sourceBody547_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody547_0 sourceBody547_74

def sourceBody547_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody547_31 sourceBody547_75

def sourceBody547_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody547_0 sourceBody547_76

def sourceBody547_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody547_30 sourceBody547_77

def sourceBody547_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody547_14 sourceBody547_78

def sourceBody547_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody547_0 sourceBody547_79

def sourceBody547_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody547_13 sourceBody547_80

def sourceBody547_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody547_5 sourceBody547_81

def sourceBody547_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody547_0 sourceBody547_82

def sourceBody547_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody547_0 sourceBody547_83

def sourceBody547_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody547_0 sourceBody547_84

def sourceBody547_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody547_0 sourceBody547_85

def sourceBody547_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody547_0 sourceBody547_86

def sourceBody547_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody547_0 sourceBody547_87

def sourceBody547_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody547_0 sourceBody547_88

def sourceBody547_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody547_0 sourceBody547_89

def source547 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (547, 1, sourceBody547_90)
end InitECandidate.Proofs.WordStages
