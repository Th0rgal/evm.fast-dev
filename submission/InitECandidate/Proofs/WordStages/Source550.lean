import InitECandidate.Proofs.WordStages.Source534
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody550_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody550_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody550_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([8, 20, 4, 16]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody550_0, 550, 2)) (some 471) ([]) (some (12, sourceBody550_1, 550, 3))

def sourceBody550_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody550_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody550_2 sourceBody550_3

def sourceBody550_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody550_4 sourceBody550_0

def sourceBody550_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 8)

def sourceBody550_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 20)

def sourceBody550_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 4)

def sourceBody550_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 16)

def sourceBody550_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 24

def sourceBody550_11 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody550_0, 550, 4)) (some 462) ([24, 2, 14, 10]) (some (24, sourceBody550_10, 550, 5))

def sourceBody550_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody550_11 sourceBody550_3

def sourceBody550_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody550_12 sourceBody550_0

def sourceBody550_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody550_9 sourceBody550_13

def sourceBody550_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody550_8 sourceBody550_14

def sourceBody550_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody550_7 sourceBody550_15

def sourceBody550_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody550_6 sourceBody550_16

def sourceBody550_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 12)

def sourceBody550_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 2

def sourceBody550_20 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody550_0, 550, 6)) (some 491) ([2]) (some (2, sourceBody550_19, 550, 7))

def sourceBody550_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody550_20 sourceBody550_3

def sourceBody550_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody550_21 sourceBody550_0

def sourceBody550_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody550_18 sourceBody550_22

def sourceBody550_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 24)

def sourceBody550_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody550_26 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody550_0, 550, 8)) (some 466) ([14]) (some (14, sourceBody550_25, 550, 9))

def sourceBody550_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody550_26 sourceBody550_3

def sourceBody550_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody550_27 sourceBody550_0

def sourceBody550_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody550_24 sourceBody550_28

def sourceBody550_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody550_0 sourceBody550_29

def sourceBody550_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody550_0 sourceBody550_30

def sourceBody550_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 12)

def sourceBody550_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 24)

def sourceBody550_34 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody550_0, 550, 10)) (some 492) ([14, 10]) (some (14, sourceBody550_25, 550, 11))

def sourceBody550_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody550_34 sourceBody550_3

def sourceBody550_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody550_35 sourceBody550_0

def sourceBody550_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody550_33 sourceBody550_36

def sourceBody550_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody550_32 sourceBody550_37

def sourceBody550_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody550_0 sourceBody550_38

def sourceBody550_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody550_0 sourceBody550_39

def sourceBody550_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody550_31 sourceBody550_40

def sourceBody550_42 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody550_0, 550, 12)) (some 403) ([14]) (some (14, sourceBody550_25, 550, 13))

def sourceBody550_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody550_42 sourceBody550_3

def sourceBody550_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody550_43 sourceBody550_0

def sourceBody550_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody550_32 sourceBody550_44

def sourceBody550_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody550_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 8#64],
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody550_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 8#64],
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody550_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 8#64],
        Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody550_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody550_51 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody550_0, 550, 14)) (some 472) ([10, 22, 6, 18]) (some (10, sourceBody550_50, 550, 15))

def sourceBody550_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody550_51 sourceBody550_3

def sourceBody550_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody550_52 sourceBody550_0

def sourceBody550_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody550_49 sourceBody550_53

def sourceBody550_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody550_48 sourceBody550_54

def sourceBody550_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody550_47 sourceBody550_55

def sourceBody550_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody550_46 sourceBody550_56

def sourceBody550_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody550_0 sourceBody550_57

def sourceBody550_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody550_0 sourceBody550_58

def sourceBody550_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody550_61 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody550_0, 550, 16)) (some 486) ([10]) (some (10, sourceBody550_50, 550, 17))

def sourceBody550_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody550_61 sourceBody550_3

def sourceBody550_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody550_62 sourceBody550_0

def sourceBody550_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody550_60 sourceBody550_63

def sourceBody550_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody550_0 sourceBody550_64

def sourceBody550_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody550_0 sourceBody550_65

def sourceBody550_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody550_59 sourceBody550_66

def sourceBody550_68 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody550_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [14]

def sourceBody550_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody550_69 sourceBody550_0

def sourceBody550_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody550_68 sourceBody550_70

def sourceBody550_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody550_67 sourceBody550_71

def sourceBody550_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody550_45 sourceBody550_72

def sourceBody550_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody550_0 sourceBody550_73

def sourceBody550_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody550_0 sourceBody550_74

def sourceBody550_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody550_41 sourceBody550_75

def sourceBody550_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody550_23 sourceBody550_76

def sourceBody550_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody550_0 sourceBody550_77

def sourceBody550_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody550_0 sourceBody550_78

def sourceBody550_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody550_17 sourceBody550_79

def sourceBody550_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody550_0 sourceBody550_80

def sourceBody550_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody550_0 sourceBody550_81

def sourceBody550_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody550_5 sourceBody550_82

def sourceBody550_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody550_0 sourceBody550_83

def sourceBody550_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody550_0 sourceBody550_84

def sourceBody550_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody550_0 sourceBody550_85

def sourceBody550_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody550_0 sourceBody550_86

def sourceBody550_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody550_0 sourceBody550_87

def sourceBody550_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody550_0 sourceBody550_88

def sourceBody550_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody550_0 sourceBody550_89

def sourceBody550_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody550_0 sourceBody550_90

def source550 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (550, 1, sourceBody550_91)
end InitECandidate.Proofs.WordStages
