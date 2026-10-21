import InitECandidate.Proofs.WordStages.Source242
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody258_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody258_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody258_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody258_0, 258, 2)) (some 69) ([]) (some (8, sourceBody258_1, 258, 3))

def sourceBody258_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody258_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody258_2 sourceBody258_3

def sourceBody258_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody258_4 sourceBody258_0

def sourceBody258_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 96#64)

def sourceBody258_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody258_8 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody258_0, 258, 4)) (some 68) ([14]) (some (14, sourceBody258_7, 258, 5))

def sourceBody258_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody258_8 sourceBody258_3

def sourceBody258_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody258_9 sourceBody258_0

def sourceBody258_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody258_6 sourceBody258_10

def sourceBody258_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 2)

def sourceBody258_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 20#64)

def sourceBody258_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 8)

def sourceBody258_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody258_16 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody258_0, 258, 6)) (some 242) ([10, 18, 6]) (some (10, sourceBody258_15, 258, 7))

def sourceBody258_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody258_16 sourceBody258_3

def sourceBody258_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody258_17 sourceBody258_0

def sourceBody258_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody258_14 sourceBody258_18

def sourceBody258_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody258_13 sourceBody258_19

def sourceBody258_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody258_12 sourceBody258_20

def sourceBody258_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody258_0 sourceBody258_21

def sourceBody258_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody258_0 sourceBody258_22

def sourceBody258_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 20#64])

def sourceBody258_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 48#64)

def sourceBody258_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 32#64])

def sourceBody258_27 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody258_0, 258, 8)) (some 242) ([10, 18, 6]) (some (10, sourceBody258_15, 258, 9))

def sourceBody258_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody258_27 sourceBody258_3

def sourceBody258_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody258_28 sourceBody258_0

def sourceBody258_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody258_26 sourceBody258_29

def sourceBody258_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody258_25 sourceBody258_30

def sourceBody258_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody258_24 sourceBody258_31

def sourceBody258_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody258_0 sourceBody258_32

def sourceBody258_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody258_0 sourceBody258_33

def sourceBody258_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody258_23 sourceBody258_34

def sourceBody258_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 68#64])

def sourceBody258_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 64#64])

def sourceBody258_38 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody258_0, 258, 10)) (some 242) ([10, 18, 6]) (some (10, sourceBody258_15, 258, 11))

def sourceBody258_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody258_38 sourceBody258_3

def sourceBody258_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody258_39 sourceBody258_0

def sourceBody258_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody258_37 sourceBody258_40

def sourceBody258_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody258_25 sourceBody258_41

def sourceBody258_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody258_36 sourceBody258_42

def sourceBody258_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody258_0 sourceBody258_43

def sourceBody258_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody258_0 sourceBody258_44

def sourceBody258_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody258_35 sourceBody258_45

def sourceBody258_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 8)

def sourceBody258_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 3#64)

def sourceBody258_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 3#64)

def sourceBody258_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 4)

def sourceBody258_51 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody258_0, 258, 12)) (some 235) ([10, 18, 6, 12]) (some (10, sourceBody258_15, 258, 13))

def sourceBody258_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody258_51 sourceBody258_3

def sourceBody258_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody258_52 sourceBody258_0

def sourceBody258_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody258_50 sourceBody258_53

def sourceBody258_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody258_49 sourceBody258_54

def sourceBody258_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody258_48 sourceBody258_55

def sourceBody258_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody258_47 sourceBody258_56

def sourceBody258_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody258_0 sourceBody258_57

def sourceBody258_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody258_0 sourceBody258_58

def sourceBody258_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody258_46 sourceBody258_59

def sourceBody258_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 16)

def sourceBody258_62 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody258_0, 258, 14)) (some 70) ([10]) (some (10, sourceBody258_15, 258, 15))

def sourceBody258_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody258_62 sourceBody258_3

def sourceBody258_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody258_63 sourceBody258_0

def sourceBody258_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody258_61 sourceBody258_64

def sourceBody258_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody258_0 sourceBody258_65

def sourceBody258_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody258_0 sourceBody258_66

def sourceBody258_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody258_60 sourceBody258_67

def sourceBody258_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody258_70 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [14]

def sourceBody258_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody258_70 sourceBody258_0

def sourceBody258_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody258_69 sourceBody258_71

def sourceBody258_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody258_68 sourceBody258_72

def sourceBody258_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody258_11 sourceBody258_73

def sourceBody258_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody258_0 sourceBody258_74

def sourceBody258_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody258_0 sourceBody258_75

def sourceBody258_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody258_5 sourceBody258_76

def sourceBody258_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody258_0 sourceBody258_77

def sourceBody258_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody258_0 sourceBody258_78

def source258 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (258, 3, sourceBody258_79)
end InitECandidate.Proofs.WordStages
