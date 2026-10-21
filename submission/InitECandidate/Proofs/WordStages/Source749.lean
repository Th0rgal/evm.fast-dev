import InitECandidate.Proofs.WordStages.Source733
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody749_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody749_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody749_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody749_0, 749, 2)) (some 69) ([]) (some (6, sourceBody749_1, 749, 3))

def sourceBody749_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody749_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody749_2 sourceBody749_3

def sourceBody749_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody749_4 sourceBody749_0

def sourceBody749_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 96#64)

def sourceBody749_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody749_8 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody749_0, 749, 4)) (some 68) ([10]) (some (10, sourceBody749_7, 749, 5))

def sourceBody749_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody749_8 sourceBody749_3

def sourceBody749_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody749_9 sourceBody749_0

def sourceBody749_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody749_6 sourceBody749_10

def sourceBody749_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 6)

def sourceBody749_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 192#64])

def sourceBody749_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody749_15 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody749_0, 749, 6)) (some 737) ([8, 14]) (some (8, sourceBody749_14, 749, 7))

def sourceBody749_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody749_15 sourceBody749_3

def sourceBody749_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody749_16 sourceBody749_0

def sourceBody749_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody749_13 sourceBody749_17

def sourceBody749_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody749_12 sourceBody749_18

def sourceBody749_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody749_0 sourceBody749_19

def sourceBody749_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody749_0 sourceBody749_20

def sourceBody749_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 192#64])

def sourceBody749_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 96#64])

def sourceBody749_24 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody749_0, 749, 8)) (some 725) ([8, 14]) (some (8, sourceBody749_14, 749, 9))

def sourceBody749_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody749_24 sourceBody749_3

def sourceBody749_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody749_25 sourceBody749_0

def sourceBody749_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody749_23 sourceBody749_26

def sourceBody749_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody749_22 sourceBody749_27

def sourceBody749_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody749_0 sourceBody749_28

def sourceBody749_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody749_0 sourceBody749_29

def sourceBody749_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody749_21 sourceBody749_30

def sourceBody749_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 96#64])

def sourceBody749_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 4)

def sourceBody749_34 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody749_0, 749, 10)) (some 725) ([8, 14]) (some (8, sourceBody749_14, 749, 11))

def sourceBody749_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody749_34 sourceBody749_3

def sourceBody749_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody749_35 sourceBody749_0

def sourceBody749_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody749_33 sourceBody749_36

def sourceBody749_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody749_32 sourceBody749_37

def sourceBody749_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody749_0 sourceBody749_38

def sourceBody749_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody749_0 sourceBody749_39

def sourceBody749_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody749_31 sourceBody749_40

def sourceBody749_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 2)

def sourceBody749_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 6)

def sourceBody749_44 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody749_0, 749, 12)) (some 725) ([8, 14]) (some (8, sourceBody749_14, 749, 13))

def sourceBody749_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody749_44 sourceBody749_3

def sourceBody749_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody749_45 sourceBody749_0

def sourceBody749_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody749_43 sourceBody749_46

def sourceBody749_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody749_42 sourceBody749_47

def sourceBody749_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody749_0 sourceBody749_48

def sourceBody749_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody749_0 sourceBody749_49

def sourceBody749_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody749_41 sourceBody749_50

def sourceBody749_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 12)

def sourceBody749_53 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody749_0, 749, 14)) (some 70) ([8]) (some (8, sourceBody749_14, 749, 15))

def sourceBody749_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody749_53 sourceBody749_3

def sourceBody749_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody749_54 sourceBody749_0

def sourceBody749_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody749_52 sourceBody749_55

def sourceBody749_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody749_0 sourceBody749_56

def sourceBody749_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody749_0 sourceBody749_57

def sourceBody749_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody749_51 sourceBody749_58

def sourceBody749_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody749_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [10]

def sourceBody749_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody749_61 sourceBody749_0

def sourceBody749_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody749_60 sourceBody749_62

def sourceBody749_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody749_59 sourceBody749_63

def sourceBody749_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody749_11 sourceBody749_64

def sourceBody749_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody749_0 sourceBody749_65

def sourceBody749_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody749_0 sourceBody749_66

def sourceBody749_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody749_5 sourceBody749_67

def sourceBody749_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody749_0 sourceBody749_68

def sourceBody749_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody749_0 sourceBody749_69

def source749 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (749, 3, sourceBody749_70)
end InitECandidate.Proofs.WordStages
