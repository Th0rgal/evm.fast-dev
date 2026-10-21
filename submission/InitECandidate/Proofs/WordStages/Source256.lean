import InitECandidate.Proofs.WordStages.Source240
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody256_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody256_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody256_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody256_0, 256, 2)) (some 69) ([]) (some (8, sourceBody256_1, 256, 3))

def sourceBody256_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody256_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody256_2 sourceBody256_3

def sourceBody256_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody256_4 sourceBody256_0

def sourceBody256_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 160#64)

def sourceBody256_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody256_8 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody256_0, 256, 4)) (some 68) ([14]) (some (14, sourceBody256_7, 256, 5))

def sourceBody256_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody256_8 sourceBody256_3

def sourceBody256_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody256_9 sourceBody256_0

def sourceBody256_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody256_6 sourceBody256_10

def sourceBody256_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 2)

def sourceBody256_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 48#64)

def sourceBody256_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 8)

def sourceBody256_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody256_16 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody256_0, 256, 6)) (some 242) ([10, 18, 6]) (some (10, sourceBody256_15, 256, 7))

def sourceBody256_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody256_16 sourceBody256_3

def sourceBody256_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody256_17 sourceBody256_0

def sourceBody256_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody256_14 sourceBody256_18

def sourceBody256_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody256_13 sourceBody256_19

def sourceBody256_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody256_12 sourceBody256_20

def sourceBody256_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody256_0 sourceBody256_21

def sourceBody256_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody256_0 sourceBody256_22

def sourceBody256_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 32#64])

def sourceBody256_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 48#64])

def sourceBody256_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody256_27 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody256_0, 256, 8)) (some 77) ([10, 18, 6]) (some (10, sourceBody256_15, 256, 9))

def sourceBody256_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody256_27 sourceBody256_3

def sourceBody256_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody256_28 sourceBody256_0

def sourceBody256_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody256_26 sourceBody256_29

def sourceBody256_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody256_25 sourceBody256_30

def sourceBody256_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody256_24 sourceBody256_31

def sourceBody256_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody256_0 sourceBody256_32

def sourceBody256_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody256_0 sourceBody256_33

def sourceBody256_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody256_23 sourceBody256_34

def sourceBody256_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 80#64])

def sourceBody256_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 64#64])

def sourceBody256_38 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody256_0, 256, 10)) (some 244) ([10, 18]) (some (10, sourceBody256_15, 256, 11))

def sourceBody256_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody256_38 sourceBody256_3

def sourceBody256_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody256_39 sourceBody256_0

def sourceBody256_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody256_37 sourceBody256_40

def sourceBody256_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody256_36 sourceBody256_41

def sourceBody256_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody256_0 sourceBody256_42

def sourceBody256_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody256_0 sourceBody256_43

def sourceBody256_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody256_35 sourceBody256_44

def sourceBody256_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 88#64])

def sourceBody256_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 96#64)

def sourceBody256_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 96#64])

def sourceBody256_49 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody256_0, 256, 12)) (some 242) ([10, 18, 6]) (some (10, sourceBody256_15, 256, 13))

def sourceBody256_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody256_49 sourceBody256_3

def sourceBody256_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody256_50 sourceBody256_0

def sourceBody256_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody256_48 sourceBody256_51

def sourceBody256_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody256_47 sourceBody256_52

def sourceBody256_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody256_46 sourceBody256_53

def sourceBody256_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody256_0 sourceBody256_54

def sourceBody256_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody256_0 sourceBody256_55

def sourceBody256_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody256_45 sourceBody256_56

def sourceBody256_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 184#64])

def sourceBody256_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 128#64])

def sourceBody256_60 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody256_0, 256, 14)) (some 244) ([10, 18]) (some (10, sourceBody256_15, 256, 15))

def sourceBody256_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody256_60 sourceBody256_3

def sourceBody256_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody256_61 sourceBody256_0

def sourceBody256_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody256_59 sourceBody256_62

def sourceBody256_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody256_58 sourceBody256_63

def sourceBody256_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody256_0 sourceBody256_64

def sourceBody256_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody256_0 sourceBody256_65

def sourceBody256_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody256_57 sourceBody256_66

def sourceBody256_68 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 8)

def sourceBody256_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 5#64)

def sourceBody256_70 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 5#64)

def sourceBody256_71 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 4)

def sourceBody256_72 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody256_0, 256, 16)) (some 235) ([10, 18, 6, 12]) (some (10, sourceBody256_15, 256, 17))

def sourceBody256_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody256_72 sourceBody256_3

def sourceBody256_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody256_73 sourceBody256_0

def sourceBody256_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody256_71 sourceBody256_74

def sourceBody256_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody256_70 sourceBody256_75

def sourceBody256_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody256_69 sourceBody256_76

def sourceBody256_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody256_68 sourceBody256_77

def sourceBody256_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody256_0 sourceBody256_78

def sourceBody256_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody256_0 sourceBody256_79

def sourceBody256_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody256_67 sourceBody256_80

def sourceBody256_82 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 16)

def sourceBody256_83 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody256_0, 256, 18)) (some 70) ([10]) (some (10, sourceBody256_15, 256, 19))

def sourceBody256_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody256_83 sourceBody256_3

def sourceBody256_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody256_84 sourceBody256_0

def sourceBody256_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody256_82 sourceBody256_85

def sourceBody256_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody256_0 sourceBody256_86

def sourceBody256_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody256_0 sourceBody256_87

def sourceBody256_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody256_81 sourceBody256_88

def sourceBody256_90 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody256_91 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [14]

def sourceBody256_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody256_91 sourceBody256_0

def sourceBody256_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody256_90 sourceBody256_92

def sourceBody256_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody256_89 sourceBody256_93

def sourceBody256_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody256_11 sourceBody256_94

def sourceBody256_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody256_0 sourceBody256_95

def sourceBody256_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody256_0 sourceBody256_96

def sourceBody256_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody256_5 sourceBody256_97

def sourceBody256_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody256_0 sourceBody256_98

def sourceBody256_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody256_0 sourceBody256_99

def source256 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (256, 3, sourceBody256_100)
end InitECandidate.Proofs.WordStages
