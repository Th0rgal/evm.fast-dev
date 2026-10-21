import InitECandidate.Proofs.WordStages.Source241
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody257_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody257_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody257_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody257_0, 257, 2)) (some 69) ([]) (some (8, sourceBody257_1, 257, 3))

def sourceBody257_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody257_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody257_2 sourceBody257_3

def sourceBody257_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody257_4 sourceBody257_0

def sourceBody257_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 96#64)

def sourceBody257_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody257_8 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody257_0, 257, 4)) (some 68) ([14]) (some (14, sourceBody257_7, 257, 5))

def sourceBody257_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody257_8 sourceBody257_3

def sourceBody257_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody257_9 sourceBody257_0

def sourceBody257_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody257_6 sourceBody257_10

def sourceBody257_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 2)

def sourceBody257_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 20#64)

def sourceBody257_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 8)

def sourceBody257_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody257_16 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody257_0, 257, 6)) (some 242) ([10, 18, 6]) (some (10, sourceBody257_15, 257, 7))

def sourceBody257_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody257_16 sourceBody257_3

def sourceBody257_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody257_17 sourceBody257_0

def sourceBody257_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody257_14 sourceBody257_18

def sourceBody257_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody257_13 sourceBody257_19

def sourceBody257_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody257_12 sourceBody257_20

def sourceBody257_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody257_0 sourceBody257_21

def sourceBody257_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody257_0 sourceBody257_22

def sourceBody257_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 20#64])

def sourceBody257_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 48#64)

def sourceBody257_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 32#64])

def sourceBody257_27 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody257_0, 257, 8)) (some 242) ([10, 18, 6]) (some (10, sourceBody257_15, 257, 9))

def sourceBody257_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody257_27 sourceBody257_3

def sourceBody257_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody257_28 sourceBody257_0

def sourceBody257_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody257_26 sourceBody257_29

def sourceBody257_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody257_25 sourceBody257_30

def sourceBody257_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody257_24 sourceBody257_31

def sourceBody257_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody257_0 sourceBody257_32

def sourceBody257_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody257_0 sourceBody257_33

def sourceBody257_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody257_23 sourceBody257_34

def sourceBody257_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 68#64])

def sourceBody257_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 64#64])

def sourceBody257_38 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody257_0, 257, 10)) (some 244) ([10, 18]) (some (10, sourceBody257_15, 257, 11))

def sourceBody257_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody257_38 sourceBody257_3

def sourceBody257_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody257_39 sourceBody257_0

def sourceBody257_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody257_37 sourceBody257_40

def sourceBody257_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody257_36 sourceBody257_41

def sourceBody257_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody257_0 sourceBody257_42

def sourceBody257_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody257_0 sourceBody257_43

def sourceBody257_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody257_35 sourceBody257_44

def sourceBody257_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 8)

def sourceBody257_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 3#64)

def sourceBody257_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 3#64)

def sourceBody257_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 4)

def sourceBody257_50 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody257_0, 257, 12)) (some 235) ([10, 18, 6, 12]) (some (10, sourceBody257_15, 257, 13))

def sourceBody257_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody257_50 sourceBody257_3

def sourceBody257_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody257_51 sourceBody257_0

def sourceBody257_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody257_49 sourceBody257_52

def sourceBody257_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody257_48 sourceBody257_53

def sourceBody257_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody257_47 sourceBody257_54

def sourceBody257_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody257_46 sourceBody257_55

def sourceBody257_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody257_0 sourceBody257_56

def sourceBody257_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody257_0 sourceBody257_57

def sourceBody257_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody257_45 sourceBody257_58

def sourceBody257_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 16)

def sourceBody257_61 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody257_0, 257, 14)) (some 70) ([10]) (some (10, sourceBody257_15, 257, 15))

def sourceBody257_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody257_61 sourceBody257_3

def sourceBody257_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody257_62 sourceBody257_0

def sourceBody257_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody257_60 sourceBody257_63

def sourceBody257_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody257_0 sourceBody257_64

def sourceBody257_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody257_0 sourceBody257_65

def sourceBody257_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody257_59 sourceBody257_66

def sourceBody257_68 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody257_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [14]

def sourceBody257_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody257_69 sourceBody257_0

def sourceBody257_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody257_68 sourceBody257_70

def sourceBody257_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody257_67 sourceBody257_71

def sourceBody257_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody257_11 sourceBody257_72

def sourceBody257_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody257_0 sourceBody257_73

def sourceBody257_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody257_0 sourceBody257_74

def sourceBody257_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody257_5 sourceBody257_75

def sourceBody257_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody257_0 sourceBody257_76

def sourceBody257_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody257_0 sourceBody257_77

def source257 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (257, 3, sourceBody257_78)
end InitECandidate.Proofs.WordStages
