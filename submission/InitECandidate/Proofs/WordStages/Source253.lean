import InitECandidate.Proofs.WordStages.Source237
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody253_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody253_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody253_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody253_0, 253, 2)) (some 69) ([]) (some (8, sourceBody253_1, 253, 3))

def sourceBody253_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody253_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody253_2 sourceBody253_3

def sourceBody253_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody253_4 sourceBody253_0

def sourceBody253_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 128#64)

def sourceBody253_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody253_8 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody253_0, 253, 4)) (some 68) ([14]) (some (14, sourceBody253_7, 253, 5))

def sourceBody253_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody253_8 sourceBody253_3

def sourceBody253_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody253_9 sourceBody253_0

def sourceBody253_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody253_6 sourceBody253_10

def sourceBody253_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 2)

def sourceBody253_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 8)

def sourceBody253_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody253_15 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody253_0, 253, 6)) (some 244) ([10, 18]) (some (10, sourceBody253_14, 253, 7))

def sourceBody253_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody253_15 sourceBody253_3

def sourceBody253_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody253_16 sourceBody253_0

def sourceBody253_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody253_13 sourceBody253_17

def sourceBody253_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody253_12 sourceBody253_18

def sourceBody253_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody253_0 sourceBody253_19

def sourceBody253_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody253_0 sourceBody253_20

def sourceBody253_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 8#64])

def sourceBody253_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 32#64])

def sourceBody253_24 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody253_0, 253, 8)) (some 244) ([10, 18]) (some (10, sourceBody253_14, 253, 9))

def sourceBody253_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody253_24 sourceBody253_3

def sourceBody253_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody253_25 sourceBody253_0

def sourceBody253_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody253_23 sourceBody253_26

def sourceBody253_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody253_22 sourceBody253_27

def sourceBody253_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody253_0 sourceBody253_28

def sourceBody253_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody253_0 sourceBody253_29

def sourceBody253_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody253_21 sourceBody253_30

def sourceBody253_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 16#64])

def sourceBody253_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 20#64)

def sourceBody253_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 64#64])

def sourceBody253_35 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody253_0, 253, 10)) (some 242) ([10, 18, 6]) (some (10, sourceBody253_14, 253, 11))

def sourceBody253_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody253_35 sourceBody253_3

def sourceBody253_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody253_36 sourceBody253_0

def sourceBody253_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody253_34 sourceBody253_37

def sourceBody253_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody253_33 sourceBody253_38

def sourceBody253_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody253_32 sourceBody253_39

def sourceBody253_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody253_0 sourceBody253_40

def sourceBody253_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody253_0 sourceBody253_41

def sourceBody253_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody253_31 sourceBody253_42

def sourceBody253_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 36#64])

def sourceBody253_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 96#64])

def sourceBody253_46 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody253_0, 253, 12)) (some 244) ([10, 18]) (some (10, sourceBody253_14, 253, 13))

def sourceBody253_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody253_46 sourceBody253_3

def sourceBody253_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody253_47 sourceBody253_0

def sourceBody253_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody253_45 sourceBody253_48

def sourceBody253_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody253_44 sourceBody253_49

def sourceBody253_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody253_0 sourceBody253_50

def sourceBody253_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody253_0 sourceBody253_51

def sourceBody253_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody253_43 sourceBody253_52

def sourceBody253_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 8)

def sourceBody253_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 4#64)

def sourceBody253_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 4#64)

def sourceBody253_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 4)

def sourceBody253_58 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody253_0, 253, 14)) (some 235) ([10, 18, 6, 12]) (some (10, sourceBody253_14, 253, 15))

def sourceBody253_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody253_58 sourceBody253_3

def sourceBody253_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody253_59 sourceBody253_0

def sourceBody253_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody253_57 sourceBody253_60

def sourceBody253_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody253_56 sourceBody253_61

def sourceBody253_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody253_55 sourceBody253_62

def sourceBody253_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody253_54 sourceBody253_63

def sourceBody253_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody253_0 sourceBody253_64

def sourceBody253_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody253_0 sourceBody253_65

def sourceBody253_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody253_53 sourceBody253_66

def sourceBody253_68 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 16)

def sourceBody253_69 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody253_0, 253, 16)) (some 70) ([10]) (some (10, sourceBody253_14, 253, 17))

def sourceBody253_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody253_69 sourceBody253_3

def sourceBody253_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody253_70 sourceBody253_0

def sourceBody253_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody253_68 sourceBody253_71

def sourceBody253_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody253_0 sourceBody253_72

def sourceBody253_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody253_0 sourceBody253_73

def sourceBody253_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody253_67 sourceBody253_74

def sourceBody253_76 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody253_77 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [14]

def sourceBody253_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody253_77 sourceBody253_0

def sourceBody253_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody253_76 sourceBody253_78

def sourceBody253_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody253_75 sourceBody253_79

def sourceBody253_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody253_11 sourceBody253_80

def sourceBody253_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody253_0 sourceBody253_81

def sourceBody253_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody253_0 sourceBody253_82

def sourceBody253_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody253_5 sourceBody253_83

def sourceBody253_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody253_0 sourceBody253_84

def sourceBody253_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody253_0 sourceBody253_85

def source253 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (253, 3, sourceBody253_86)
end InitECandidate.Proofs.WordStages
