import InitECandidate.Proofs.WordStages.Source512
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody528_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody528_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody528_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([8, 22, 4, 18]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody528_0, 528, 2)) (some 471) ([]) (some (12, sourceBody528_1, 528, 3))

def sourceBody528_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody528_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody528_2 sourceBody528_3

def sourceBody528_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody528_4 sourceBody528_0

def sourceBody528_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 3#64)

def sourceBody528_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 8)

def sourceBody528_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 22)

def sourceBody528_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 4)

def sourceBody528_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 18)

def sourceBody528_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody528_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody528_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody528_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody528_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 26

def sourceBody528_16 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody528_0, 528, 4)) (some 479) ([26, 2, 16, 10, 24, 6, 20, 14, 28]) (some (26, sourceBody528_15, 528, 5))

def sourceBody528_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody528_16 sourceBody528_3

def sourceBody528_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody528_17 sourceBody528_0

def sourceBody528_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody528_14 sourceBody528_18

def sourceBody528_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody528_13 sourceBody528_19

def sourceBody528_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody528_12 sourceBody528_20

def sourceBody528_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody528_11 sourceBody528_21

def sourceBody528_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody528_10 sourceBody528_22

def sourceBody528_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody528_9 sourceBody528_23

def sourceBody528_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody528_8 sourceBody528_24

def sourceBody528_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody528_7 sourceBody528_25

def sourceBody528_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody528_6 sourceBody528_26

def sourceBody528_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody528_0 sourceBody528_27

def sourceBody528_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody528_0 sourceBody528_28

def sourceBody528_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 8)

def sourceBody528_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 22)

def sourceBody528_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 4)

def sourceBody528_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 18)

def sourceBody528_34 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody528_0, 528, 6)) (some 458) ([26, 2, 16, 10]) (some (26, sourceBody528_15, 528, 7))

def sourceBody528_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody528_34 sourceBody528_3

def sourceBody528_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody528_35 sourceBody528_0

def sourceBody528_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody528_33 sourceBody528_36

def sourceBody528_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody528_32 sourceBody528_37

def sourceBody528_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody528_31 sourceBody528_38

def sourceBody528_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody528_30 sourceBody528_39

def sourceBody528_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
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

def sourceBody528_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 24

def sourceBody528_43 : WordLangProgHOL (BitVec 64) :=
.call (some (([26, 2, 16, 10]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody528_0, 528, 8)) (some 146) ([24, 6]) (some (24, sourceBody528_42, 528, 9))

def sourceBody528_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody528_43 sourceBody528_3

def sourceBody528_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody528_44 sourceBody528_0

def sourceBody528_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody528_11 sourceBody528_45

def sourceBody528_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody528_41 sourceBody528_46

def sourceBody528_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 26)

def sourceBody528_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 2)

def sourceBody528_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 16)

def sourceBody528_51 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 10)

def sourceBody528_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody528_53 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody528_0, 528, 10)) (some 472) ([6, 20, 14, 28]) (some (6, sourceBody528_52, 528, 11))

def sourceBody528_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody528_53 sourceBody528_3

def sourceBody528_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody528_54 sourceBody528_0

def sourceBody528_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody528_51 sourceBody528_55

def sourceBody528_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody528_50 sourceBody528_56

def sourceBody528_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody528_49 sourceBody528_57

def sourceBody528_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody528_48 sourceBody528_58

def sourceBody528_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody528_0 sourceBody528_59

def sourceBody528_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody528_0 sourceBody528_60

def sourceBody528_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody528_63 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody528_0, 528, 12)) (some 486) ([6]) (some (6, sourceBody528_52, 528, 13))

def sourceBody528_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody528_63 sourceBody528_3

def sourceBody528_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody528_64 sourceBody528_0

def sourceBody528_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody528_62 sourceBody528_65

def sourceBody528_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody528_0 sourceBody528_66

def sourceBody528_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody528_0 sourceBody528_67

def sourceBody528_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody528_61 sourceBody528_68

def sourceBody528_70 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody528_71 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [24]

def sourceBody528_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody528_71 sourceBody528_0

def sourceBody528_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody528_70 sourceBody528_72

def sourceBody528_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody528_69 sourceBody528_73

def sourceBody528_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody528_47 sourceBody528_74

def sourceBody528_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody528_0 sourceBody528_75

def sourceBody528_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody528_0 sourceBody528_76

def sourceBody528_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody528_0 sourceBody528_77

def sourceBody528_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody528_0 sourceBody528_78

def sourceBody528_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody528_0 sourceBody528_79

def sourceBody528_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody528_0 sourceBody528_80

def sourceBody528_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody528_0 sourceBody528_81

def sourceBody528_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody528_0 sourceBody528_82

def sourceBody528_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody528_40 sourceBody528_83

def sourceBody528_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody528_0 sourceBody528_84

def sourceBody528_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody528_0 sourceBody528_85

def sourceBody528_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody528_29 sourceBody528_86

def sourceBody528_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody528_5 sourceBody528_87

def sourceBody528_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody528_0 sourceBody528_88

def sourceBody528_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody528_0 sourceBody528_89

def sourceBody528_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody528_0 sourceBody528_90

def sourceBody528_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody528_0 sourceBody528_91

def sourceBody528_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody528_0 sourceBody528_92

def sourceBody528_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody528_0 sourceBody528_93

def sourceBody528_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody528_0 sourceBody528_94

def sourceBody528_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody528_0 sourceBody528_95

def source528 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (528, 1, sourceBody528_96)
end InitECandidate.Proofs.WordStages
