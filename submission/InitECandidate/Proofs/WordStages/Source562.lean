import InitECandidate.Proofs.WordStages.Source546
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody562_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody562_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody562_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([6, 16, 4, 14]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody562_0, 562, 2)) (some 471) ([]) (some (10, sourceBody562_1, 562, 3))

def sourceBody562_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody562_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody562_2 sourceBody562_3

def sourceBody562_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody562_4 sourceBody562_0

def sourceBody562_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 6)

def sourceBody562_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 16)

def sourceBody562_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 4)

def sourceBody562_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 14)

def sourceBody562_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody562_11 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody562_0, 562, 4)) (some 462) ([20, 2, 12, 8]) (some (20, sourceBody562_10, 562, 5))

def sourceBody562_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody562_11 sourceBody562_3

def sourceBody562_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody562_12 sourceBody562_0

def sourceBody562_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody562_9 sourceBody562_13

def sourceBody562_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody562_8 sourceBody562_14

def sourceBody562_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody562_7 sourceBody562_15

def sourceBody562_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody562_6 sourceBody562_16

def sourceBody562_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 10)

def sourceBody562_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 2

def sourceBody562_20 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody562_0, 562, 6)) (some 491) ([2]) (some (2, sourceBody562_19, 562, 7))

def sourceBody562_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody562_20 sourceBody562_3

def sourceBody562_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody562_21 sourceBody562_0

def sourceBody562_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody562_18 sourceBody562_22

def sourceBody562_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 20, Flapjack.WordLangExpHOL.const 100#64])

def sourceBody562_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody562_26 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody562_0, 562, 8)) (some 466) ([12]) (some (12, sourceBody562_25, 562, 9))

def sourceBody562_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody562_26 sourceBody562_3

def sourceBody562_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody562_27 sourceBody562_0

def sourceBody562_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody562_24 sourceBody562_28

def sourceBody562_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody562_0 sourceBody562_29

def sourceBody562_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody562_0 sourceBody562_30

def sourceBody562_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 10)

def sourceBody562_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 20)

def sourceBody562_34 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody562_0, 562, 10)) (some 492) ([12, 8]) (some (12, sourceBody562_25, 562, 11))

def sourceBody562_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody562_34 sourceBody562_3

def sourceBody562_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody562_35 sourceBody562_0

def sourceBody562_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody562_33 sourceBody562_36

def sourceBody562_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody562_32 sourceBody562_37

def sourceBody562_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody562_0 sourceBody562_38

def sourceBody562_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody562_0 sourceBody562_39

def sourceBody562_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody562_31 sourceBody562_40

def sourceBody562_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 10)

def sourceBody562_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody562_44 : WordLangProgHOL (BitVec 64) :=
.call (some (([2, 12]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody562_0, 562, 12)) (some 561) ([8]) (some (8, sourceBody562_43, 562, 13))

def sourceBody562_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody562_44 sourceBody562_3

def sourceBody562_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody562_45 sourceBody562_0

def sourceBody562_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody562_42 sourceBody562_46

def sourceBody562_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 12)

def sourceBody562_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody562_50 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody562_0, 562, 14)) (some 473) ([18]) (some (18, sourceBody562_49, 562, 15))

def sourceBody562_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody562_50 sourceBody562_3

def sourceBody562_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody562_51 sourceBody562_0

def sourceBody562_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody562_48 sourceBody562_52

def sourceBody562_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody562_0 sourceBody562_53

def sourceBody562_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody562_0 sourceBody562_54

def sourceBody562_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody562_57 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody562_0, 562, 16)) (some 486) ([18]) (some (18, sourceBody562_49, 562, 17))

def sourceBody562_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody562_57 sourceBody562_3

def sourceBody562_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody562_58 sourceBody562_0

def sourceBody562_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody562_56 sourceBody562_59

def sourceBody562_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody562_0 sourceBody562_60

def sourceBody562_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody562_0 sourceBody562_61

def sourceBody562_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody562_55 sourceBody562_62

def sourceBody562_64 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody562_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [8]

def sourceBody562_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody562_65 sourceBody562_0

def sourceBody562_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody562_64 sourceBody562_66

def sourceBody562_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody562_63 sourceBody562_67

def sourceBody562_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody562_47 sourceBody562_68

def sourceBody562_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody562_0 sourceBody562_69

def sourceBody562_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody562_0 sourceBody562_70

def sourceBody562_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody562_0 sourceBody562_71

def sourceBody562_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody562_0 sourceBody562_72

def sourceBody562_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody562_41 sourceBody562_73

def sourceBody562_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody562_23 sourceBody562_74

def sourceBody562_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody562_0 sourceBody562_75

def sourceBody562_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody562_0 sourceBody562_76

def sourceBody562_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody562_17 sourceBody562_77

def sourceBody562_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody562_0 sourceBody562_78

def sourceBody562_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody562_0 sourceBody562_79

def sourceBody562_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody562_5 sourceBody562_80

def sourceBody562_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody562_0 sourceBody562_81

def sourceBody562_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody562_0 sourceBody562_82

def sourceBody562_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody562_0 sourceBody562_83

def sourceBody562_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody562_0 sourceBody562_84

def sourceBody562_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody562_0 sourceBody562_85

def sourceBody562_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody562_0 sourceBody562_86

def sourceBody562_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody562_0 sourceBody562_87

def sourceBody562_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody562_0 sourceBody562_88

def source562 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (562, 1, sourceBody562_89)
end InitECandidate.Proofs.WordStages
