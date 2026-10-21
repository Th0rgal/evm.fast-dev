import InitECandidate.Proofs.WordStages.Source243
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody259_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody259_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody259_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody259_0, 259, 2)) (some 69) ([]) (some (8, sourceBody259_1, 259, 3))

def sourceBody259_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody259_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody259_2 sourceBody259_3

def sourceBody259_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody259_4 sourceBody259_0

def sourceBody259_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 128#64)

def sourceBody259_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody259_8 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody259_0, 259, 4)) (some 68) ([14]) (some (14, sourceBody259_7, 259, 5))

def sourceBody259_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody259_8 sourceBody259_3

def sourceBody259_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody259_9 sourceBody259_0

def sourceBody259_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody259_6 sourceBody259_10

def sourceBody259_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 2)

def sourceBody259_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 48#64)

def sourceBody259_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 8)

def sourceBody259_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody259_16 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody259_0, 259, 6)) (some 242) ([10, 18, 6]) (some (10, sourceBody259_15, 259, 7))

def sourceBody259_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody259_16 sourceBody259_3

def sourceBody259_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody259_17 sourceBody259_0

def sourceBody259_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody259_14 sourceBody259_18

def sourceBody259_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody259_13 sourceBody259_19

def sourceBody259_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody259_12 sourceBody259_20

def sourceBody259_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody259_0 sourceBody259_21

def sourceBody259_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody259_0 sourceBody259_22

def sourceBody259_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 32#64])

def sourceBody259_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 48#64])

def sourceBody259_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody259_27 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody259_0, 259, 8)) (some 77) ([10, 18, 6]) (some (10, sourceBody259_15, 259, 9))

def sourceBody259_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody259_27 sourceBody259_3

def sourceBody259_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody259_28 sourceBody259_0

def sourceBody259_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody259_26 sourceBody259_29

def sourceBody259_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody259_25 sourceBody259_30

def sourceBody259_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody259_24 sourceBody259_31

def sourceBody259_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody259_0 sourceBody259_32

def sourceBody259_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody259_0 sourceBody259_33

def sourceBody259_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody259_23 sourceBody259_34

def sourceBody259_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 80#64])

def sourceBody259_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 64#64])

def sourceBody259_38 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody259_0, 259, 10)) (some 244) ([10, 18]) (some (10, sourceBody259_15, 259, 11))

def sourceBody259_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody259_38 sourceBody259_3

def sourceBody259_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody259_39 sourceBody259_0

def sourceBody259_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody259_37 sourceBody259_40

def sourceBody259_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody259_36 sourceBody259_41

def sourceBody259_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody259_0 sourceBody259_42

def sourceBody259_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody259_0 sourceBody259_43

def sourceBody259_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody259_35 sourceBody259_44

def sourceBody259_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 88#64])

def sourceBody259_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 96#64)

def sourceBody259_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 96#64])

def sourceBody259_49 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody259_0, 259, 12)) (some 242) ([10, 18, 6]) (some (10, sourceBody259_15, 259, 13))

def sourceBody259_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody259_49 sourceBody259_3

def sourceBody259_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody259_50 sourceBody259_0

def sourceBody259_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody259_48 sourceBody259_51

def sourceBody259_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody259_47 sourceBody259_52

def sourceBody259_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody259_46 sourceBody259_53

def sourceBody259_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody259_0 sourceBody259_54

def sourceBody259_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody259_0 sourceBody259_55

def sourceBody259_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody259_45 sourceBody259_56

def sourceBody259_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 8)

def sourceBody259_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 4#64)

def sourceBody259_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 4#64)

def sourceBody259_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 4)

def sourceBody259_62 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody259_0, 259, 14)) (some 235) ([10, 18, 6, 12]) (some (10, sourceBody259_15, 259, 15))

def sourceBody259_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody259_62 sourceBody259_3

def sourceBody259_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody259_63 sourceBody259_0

def sourceBody259_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody259_61 sourceBody259_64

def sourceBody259_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody259_60 sourceBody259_65

def sourceBody259_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody259_59 sourceBody259_66

def sourceBody259_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody259_58 sourceBody259_67

def sourceBody259_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody259_0 sourceBody259_68

def sourceBody259_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody259_0 sourceBody259_69

def sourceBody259_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody259_57 sourceBody259_70

def sourceBody259_72 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 16)

def sourceBody259_73 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody259_0, 259, 16)) (some 70) ([10]) (some (10, sourceBody259_15, 259, 17))

def sourceBody259_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody259_73 sourceBody259_3

def sourceBody259_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody259_74 sourceBody259_0

def sourceBody259_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody259_72 sourceBody259_75

def sourceBody259_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody259_0 sourceBody259_76

def sourceBody259_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody259_0 sourceBody259_77

def sourceBody259_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody259_71 sourceBody259_78

def sourceBody259_80 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody259_81 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [14]

def sourceBody259_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody259_81 sourceBody259_0

def sourceBody259_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody259_80 sourceBody259_82

def sourceBody259_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody259_79 sourceBody259_83

def sourceBody259_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody259_11 sourceBody259_84

def sourceBody259_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody259_0 sourceBody259_85

def sourceBody259_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody259_0 sourceBody259_86

def sourceBody259_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody259_5 sourceBody259_87

def sourceBody259_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody259_0 sourceBody259_88

def sourceBody259_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody259_0 sourceBody259_89

def source259 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (259, 3, sourceBody259_90)
end InitECandidate.Proofs.WordStages
