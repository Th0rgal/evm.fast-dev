import InitECandidate.Proofs.WordStages.Source768
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody784_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody784_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody784_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody784_0, 784, 2)) (some 69) ([]) (some (6, sourceBody784_1, 784, 3))

def sourceBody784_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody784_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody784_2 sourceBody784_3

def sourceBody784_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody784_4 sourceBody784_0

def sourceBody784_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 192#64)

def sourceBody784_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody784_8 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody784_0, 784, 4)) (some 68) ([10]) (some (10, sourceBody784_7, 784, 5))

def sourceBody784_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody784_8 sourceBody784_3

def sourceBody784_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody784_9 sourceBody784_0

def sourceBody784_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody784_6 sourceBody784_10

def sourceBody784_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 6)

def sourceBody784_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 2)

def sourceBody784_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody784_15 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody784_0, 784, 6)) (some 781) ([8, 14]) (some (8, sourceBody784_14, 784, 7))

def sourceBody784_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody784_15 sourceBody784_3

def sourceBody784_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody784_16 sourceBody784_0

def sourceBody784_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody784_13 sourceBody784_17

def sourceBody784_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody784_12 sourceBody784_18

def sourceBody784_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody784_0 sourceBody784_19

def sourceBody784_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody784_0 sourceBody784_20

def sourceBody784_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 4)

def sourceBody784_23 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody784_0, 784, 8)) (some 724) ([8, 14]) (some (8, sourceBody784_14, 784, 9))

def sourceBody784_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody784_23 sourceBody784_3

def sourceBody784_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody784_24 sourceBody784_0

def sourceBody784_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody784_22 sourceBody784_25

def sourceBody784_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody784_12 sourceBody784_26

def sourceBody784_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody784_0 sourceBody784_27

def sourceBody784_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody784_0 sourceBody784_28

def sourceBody784_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody784_21 sourceBody784_29

def sourceBody784_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 48#64])

def sourceBody784_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 64#64])

def sourceBody784_33 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody784_0, 784, 10)) (some 724) ([8, 14]) (some (8, sourceBody784_14, 784, 11))

def sourceBody784_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody784_33 sourceBody784_3

def sourceBody784_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody784_34 sourceBody784_0

def sourceBody784_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody784_32 sourceBody784_35

def sourceBody784_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody784_31 sourceBody784_36

def sourceBody784_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody784_0 sourceBody784_37

def sourceBody784_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody784_0 sourceBody784_38

def sourceBody784_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody784_30 sourceBody784_39

def sourceBody784_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 96#64])

def sourceBody784_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 128#64])

def sourceBody784_43 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody784_0, 784, 12)) (some 724) ([8, 14]) (some (8, sourceBody784_14, 784, 13))

def sourceBody784_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody784_43 sourceBody784_3

def sourceBody784_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody784_44 sourceBody784_0

def sourceBody784_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody784_42 sourceBody784_45

def sourceBody784_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody784_41 sourceBody784_46

def sourceBody784_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody784_0 sourceBody784_47

def sourceBody784_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody784_0 sourceBody784_48

def sourceBody784_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody784_40 sourceBody784_49

def sourceBody784_51 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 144#64])

def sourceBody784_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 192#64])

def sourceBody784_53 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody784_0, 784, 14)) (some 724) ([8, 14]) (some (8, sourceBody784_14, 784, 15))

def sourceBody784_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody784_53 sourceBody784_3

def sourceBody784_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody784_54 sourceBody784_0

def sourceBody784_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody784_52 sourceBody784_55

def sourceBody784_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody784_51 sourceBody784_56

def sourceBody784_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody784_0 sourceBody784_57

def sourceBody784_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody784_0 sourceBody784_58

def sourceBody784_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody784_50 sourceBody784_59

def sourceBody784_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 12)

def sourceBody784_62 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody784_0, 784, 16)) (some 70) ([8]) (some (8, sourceBody784_14, 784, 17))

def sourceBody784_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody784_62 sourceBody784_3

def sourceBody784_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody784_63 sourceBody784_0

def sourceBody784_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody784_61 sourceBody784_64

def sourceBody784_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody784_0 sourceBody784_65

def sourceBody784_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody784_0 sourceBody784_66

def sourceBody784_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody784_60 sourceBody784_67

def sourceBody784_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody784_70 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [10]

def sourceBody784_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody784_70 sourceBody784_0

def sourceBody784_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody784_69 sourceBody784_71

def sourceBody784_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody784_68 sourceBody784_72

def sourceBody784_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody784_11 sourceBody784_73

def sourceBody784_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody784_0 sourceBody784_74

def sourceBody784_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody784_0 sourceBody784_75

def sourceBody784_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody784_5 sourceBody784_76

def sourceBody784_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody784_0 sourceBody784_77

def sourceBody784_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody784_0 sourceBody784_78

def source784 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (784, 3, sourceBody784_79)
end InitECandidate.Proofs.WordStages
