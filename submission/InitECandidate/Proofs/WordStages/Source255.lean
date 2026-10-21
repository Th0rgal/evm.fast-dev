import InitECandidate.Proofs.WordStages.Source239
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody255_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody255_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 0#64]))

def sourceBody255_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 26

def sourceBody255_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
      PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody255_0, 255, 2)) (some 69) ([]) (some (26, sourceBody255_2, 255, 3))

def sourceBody255_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody255_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_3 sourceBody255_4

def sourceBody255_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_5 sourceBody255_0

def sourceBody255_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 608#64)

def sourceBody255_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody255_9 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) (Flapjack.Spt.ls PUnit.unit))
      PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody255_0, 255, 4)) (some 68) ([18]) (some (18, sourceBody255_8, 255, 5))

def sourceBody255_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_9 sourceBody255_4

def sourceBody255_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_10 sourceBody255_0

def sourceBody255_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_7 sourceBody255_11

def sourceBody255_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 26)

def sourceBody255_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 30, Flapjack.WordLangExpHOL.const 0#64])

def sourceBody255_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody255_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 34

def sourceBody255_17 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
      PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody255_0, 255, 6)) (some 77) ([34, 8, 24]) (some (34, sourceBody255_16, 255, 7))

def sourceBody255_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_17 sourceBody255_4

def sourceBody255_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_18 sourceBody255_0

def sourceBody255_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_15 sourceBody255_19

def sourceBody255_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_14 sourceBody255_20

def sourceBody255_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_13 sourceBody255_21

def sourceBody255_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_0 sourceBody255_22

def sourceBody255_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_0 sourceBody255_23

def sourceBody255_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 30, Flapjack.WordLangExpHOL.const 32#64])

def sourceBody255_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 20#64)

def sourceBody255_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 26, Flapjack.WordLangExpHOL.const 32#64])

def sourceBody255_28 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
      PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody255_0, 255, 8)) (some 242) ([34, 8, 24]) (some (34, sourceBody255_16, 255, 9))

def sourceBody255_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_28 sourceBody255_4

def sourceBody255_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_29 sourceBody255_0

def sourceBody255_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_27 sourceBody255_30

def sourceBody255_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_26 sourceBody255_31

def sourceBody255_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_25 sourceBody255_32

def sourceBody255_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_0 sourceBody255_33

def sourceBody255_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_0 sourceBody255_34

def sourceBody255_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_24 sourceBody255_35

def sourceBody255_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 26, Flapjack.WordLangExpHOL.const 64#64])

def sourceBody255_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 30, Flapjack.WordLangExpHOL.const 52#64])

def sourceBody255_39 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
      PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody255_0, 255, 10)) (some 77) ([34, 8, 24]) (some (34, sourceBody255_16, 255, 11))

def sourceBody255_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_39 sourceBody255_4

def sourceBody255_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_40 sourceBody255_0

def sourceBody255_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_15 sourceBody255_41

def sourceBody255_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_38 sourceBody255_42

def sourceBody255_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_37 sourceBody255_43

def sourceBody255_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_0 sourceBody255_44

def sourceBody255_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_0 sourceBody255_45

def sourceBody255_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_36 sourceBody255_46

def sourceBody255_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 26, Flapjack.WordLangExpHOL.const 96#64])

def sourceBody255_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 30, Flapjack.WordLangExpHOL.const 84#64])

def sourceBody255_50 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
      PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody255_0, 255, 12)) (some 77) ([34, 8, 24]) (some (34, sourceBody255_16, 255, 13))

def sourceBody255_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_50 sourceBody255_4

def sourceBody255_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_51 sourceBody255_0

def sourceBody255_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_15 sourceBody255_52

def sourceBody255_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_49 sourceBody255_53

def sourceBody255_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_48 sourceBody255_54

def sourceBody255_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_0 sourceBody255_55

def sourceBody255_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_0 sourceBody255_56

def sourceBody255_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_47 sourceBody255_57

def sourceBody255_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 30, Flapjack.WordLangExpHOL.const 116#64])

def sourceBody255_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 256#64)

def sourceBody255_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 26, Flapjack.WordLangExpHOL.const 128#64])

def sourceBody255_62 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
      PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody255_0, 255, 14)) (some 242) ([34, 8, 24]) (some (34, sourceBody255_16, 255, 15))

def sourceBody255_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_62 sourceBody255_4

def sourceBody255_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_63 sourceBody255_0

def sourceBody255_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_61 sourceBody255_64

def sourceBody255_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_60 sourceBody255_65

def sourceBody255_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_59 sourceBody255_66

def sourceBody255_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_0 sourceBody255_67

def sourceBody255_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_0 sourceBody255_68

def sourceBody255_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_58 sourceBody255_69

def sourceBody255_71 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 26, Flapjack.WordLangExpHOL.const 160#64])

def sourceBody255_72 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 30, Flapjack.WordLangExpHOL.const 372#64])

def sourceBody255_73 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
      PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody255_0, 255, 16)) (some 77) ([34, 8, 24]) (some (34, sourceBody255_16, 255, 17))

def sourceBody255_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_73 sourceBody255_4

def sourceBody255_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_74 sourceBody255_0

def sourceBody255_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_15 sourceBody255_75

def sourceBody255_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_72 sourceBody255_76

def sourceBody255_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_71 sourceBody255_77

def sourceBody255_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_0 sourceBody255_78

def sourceBody255_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_0 sourceBody255_79

def sourceBody255_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_70 sourceBody255_80

def sourceBody255_82 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 30, Flapjack.WordLangExpHOL.const 404#64])

def sourceBody255_83 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 26, Flapjack.WordLangExpHOL.const 192#64])

def sourceBody255_84 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
      PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody255_0, 255, 18)) (some 244) ([34, 8]) (some (34, sourceBody255_16, 255, 19))

def sourceBody255_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_84 sourceBody255_4

def sourceBody255_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_85 sourceBody255_0

def sourceBody255_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_83 sourceBody255_86

def sourceBody255_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_82 sourceBody255_87

def sourceBody255_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_0 sourceBody255_88

def sourceBody255_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_0 sourceBody255_89

def sourceBody255_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_81 sourceBody255_90

def sourceBody255_92 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 30, Flapjack.WordLangExpHOL.const 412#64])

def sourceBody255_93 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 26, Flapjack.WordLangExpHOL.const 224#64])

def sourceBody255_94 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
      PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody255_0, 255, 20)) (some 244) ([34, 8]) (some (34, sourceBody255_16, 255, 21))

def sourceBody255_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_94 sourceBody255_4

def sourceBody255_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_95 sourceBody255_0

def sourceBody255_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_93 sourceBody255_96

def sourceBody255_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_92 sourceBody255_97

def sourceBody255_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_0 sourceBody255_98

def sourceBody255_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_0 sourceBody255_99

def sourceBody255_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_91 sourceBody255_100

def sourceBody255_102 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 30, Flapjack.WordLangExpHOL.const 420#64])

def sourceBody255_103 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 26, Flapjack.WordLangExpHOL.const 256#64])

def sourceBody255_104 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
      PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody255_0, 255, 22)) (some 244) ([34, 8]) (some (34, sourceBody255_16, 255, 23))

def sourceBody255_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_104 sourceBody255_4

def sourceBody255_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_105 sourceBody255_0

def sourceBody255_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_103 sourceBody255_106

def sourceBody255_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_102 sourceBody255_107

def sourceBody255_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_0 sourceBody255_108

def sourceBody255_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_0 sourceBody255_109

def sourceBody255_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_101 sourceBody255_110

def sourceBody255_112 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 30, Flapjack.WordLangExpHOL.const 428#64])

def sourceBody255_113 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 26, Flapjack.WordLangExpHOL.const 288#64])

def sourceBody255_114 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
      PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody255_0, 255, 24)) (some 244) ([34, 8]) (some (34, sourceBody255_16, 255, 25))

def sourceBody255_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_114 sourceBody255_4

def sourceBody255_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_115 sourceBody255_0

def sourceBody255_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_113 sourceBody255_116

def sourceBody255_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_112 sourceBody255_117

def sourceBody255_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_0 sourceBody255_118

def sourceBody255_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_0 sourceBody255_119

def sourceBody255_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_111 sourceBody255_120

def sourceBody255_122 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody255_123 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody255_124 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody255_125 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 26, Flapjack.WordLangExpHOL.const 320#64])

def sourceBody255_126 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
      PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody255_0, 255, 26)) (some 243) ([34, 8, 24, 16]) (some (34, sourceBody255_16, 255, 27))

def sourceBody255_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_126 sourceBody255_4

def sourceBody255_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_127 sourceBody255_0

def sourceBody255_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_125 sourceBody255_128

def sourceBody255_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_124 sourceBody255_129

def sourceBody255_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_123 sourceBody255_130

def sourceBody255_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_122 sourceBody255_131

def sourceBody255_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_0 sourceBody255_132

def sourceBody255_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_0 sourceBody255_133

def sourceBody255_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_121 sourceBody255_134

def sourceBody255_136 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 26, Flapjack.WordLangExpHOL.const 352#64])

def sourceBody255_137 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 30, Flapjack.WordLangExpHOL.const 440#64])

def sourceBody255_138 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
      PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody255_0, 255, 28)) (some 77) ([34, 8, 24]) (some (34, sourceBody255_16, 255, 29))

def sourceBody255_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_138 sourceBody255_4

def sourceBody255_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_139 sourceBody255_0

def sourceBody255_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_15 sourceBody255_140

def sourceBody255_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_137 sourceBody255_141

def sourceBody255_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_136 sourceBody255_142

def sourceBody255_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_0 sourceBody255_143

def sourceBody255_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_0 sourceBody255_144

def sourceBody255_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_135 sourceBody255_145

def sourceBody255_147 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 26, Flapjack.WordLangExpHOL.const 384#64])

def sourceBody255_148 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 30, Flapjack.WordLangExpHOL.const 472#64])

def sourceBody255_149 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
      PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody255_0, 255, 30)) (some 77) ([34, 8, 24]) (some (34, sourceBody255_16, 255, 31))

def sourceBody255_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_149 sourceBody255_4

def sourceBody255_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_150 sourceBody255_0

def sourceBody255_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_15 sourceBody255_151

def sourceBody255_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_148 sourceBody255_152

def sourceBody255_154 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_147 sourceBody255_153

def sourceBody255_155 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_0 sourceBody255_154

def sourceBody255_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_0 sourceBody255_155

def sourceBody255_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_146 sourceBody255_156

def sourceBody255_158 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 32#64]))

def sourceBody255_159 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 40#64]))

def sourceBody255_160 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 24

def sourceBody255_161 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody255_0, 255, 32)) (some 69) ([]) (some (24, sourceBody255_160, 255, 33))

def sourceBody255_162 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_161 sourceBody255_4

def sourceBody255_163 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_162 sourceBody255_0

def sourceBody255_164 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 34)
        (Flapjack.WordLangExpHOL.const 5#64),
      Flapjack.WordLangExpHOL.const 32#64])

def sourceBody255_165 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody255_166 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody255_0, 255, 34)) (some 68) ([16]) (some (16, sourceBody255_165, 255, 35))

def sourceBody255_167 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_166 sourceBody255_4

def sourceBody255_168 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_167 sourceBody255_0

def sourceBody255_169 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_164 sourceBody255_168

def sourceBody255_170 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody255_171 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 16)

def sourceBody255_172 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 34)

def sourceBody255_173 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody255_174 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody255_175 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.less) 12 (Flapjack.WordRegImm.reg 28) sourceBody255_173 sourceBody255_174

def sourceBody255_176 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_175 sourceBody255_4

def sourceBody255_177 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 12)

def sourceBody255_178 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 18,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 16)
          (Flapjack.WordLangExpHOL.const 4#64)]))

def sourceBody255_179 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 18,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 16)
          (Flapjack.WordLangExpHOL.const 4#64),
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody255_180 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 24,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 16)
        (Flapjack.WordLangExpHOL.const 5#64)])

def sourceBody255_181 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody255_182 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody255_0, 255, 36)) (some 239) ([12, 28, 20]) (some (12, sourceBody255_181, 255, 37))

def sourceBody255_183 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_182 sourceBody255_4

def sourceBody255_184 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_183 sourceBody255_0

def sourceBody255_185 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_180 sourceBody255_184

def sourceBody255_186 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_179 sourceBody255_185

def sourceBody255_187 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_178 sourceBody255_186

def sourceBody255_188 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_0 sourceBody255_187

def sourceBody255_189 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_0 sourceBody255_188

def sourceBody255_190 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 16, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody255_191 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 32)

def sourceBody255_192 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_191 sourceBody255_0

def sourceBody255_193 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_192 sourceBody255_0

def sourceBody255_194 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_190 sourceBody255_193

def sourceBody255_195 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_0 sourceBody255_194

def sourceBody255_196 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_189 sourceBody255_195

def sourceBody255_197 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody255_198 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_196 sourceBody255_197

def sourceBody255_199 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody255_200 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 20 (Flapjack.WordRegImm.imm 0#64) sourceBody255_198 sourceBody255_199

def sourceBody255_201 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_200 sourceBody255_4

def sourceBody255_202 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_201 sourceBody255_0

def sourceBody255_203 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_177 sourceBody255_202

def sourceBody255_204 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_176 sourceBody255_203

def sourceBody255_205 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_172 sourceBody255_204

def sourceBody255_206 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_171 sourceBody255_205

def sourceBody255_207 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
  PUnit.unit Flapjack.Spt.ln) sourceBody255_206 (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody255_208 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_207 sourceBody255_4

def sourceBody255_209 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_4 sourceBody255_208

def sourceBody255_210 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 24)

def sourceBody255_211 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 34)

def sourceBody255_212 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 26, Flapjack.WordLangExpHOL.const 416#64])

def sourceBody255_213 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody255_0, 255, 38)) (some 238) ([12, 28, 20, 36]) (some (12, sourceBody255_181, 255, 39))

def sourceBody255_214 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_213 sourceBody255_4

def sourceBody255_215 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_214 sourceBody255_0

def sourceBody255_216 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_212 sourceBody255_215

def sourceBody255_217 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_211 sourceBody255_216

def sourceBody255_218 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_172 sourceBody255_217

def sourceBody255_219 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_210 sourceBody255_218

def sourceBody255_220 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_0 sourceBody255_219

def sourceBody255_221 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_0 sourceBody255_220

def sourceBody255_222 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_209 sourceBody255_221

def sourceBody255_223 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 8)

def sourceBody255_224 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody255_0, 255, 40)) (some 70) ([12]) (some (12, sourceBody255_181, 255, 41))

def sourceBody255_225 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_224 sourceBody255_4

def sourceBody255_226 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_225 sourceBody255_0

def sourceBody255_227 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_223 sourceBody255_226

def sourceBody255_228 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_0 sourceBody255_227

def sourceBody255_229 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_0 sourceBody255_228

def sourceBody255_230 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_222 sourceBody255_229

def sourceBody255_231 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 48#64]))

def sourceBody255_232 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 56#64]))

def sourceBody255_233 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 12)
        (Flapjack.WordLangExpHOL.const 5#64),
      Flapjack.WordLangExpHOL.const 32#64])

def sourceBody255_234 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 28

def sourceBody255_235 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody255_0, 255, 42)) (some 68) ([28]) (some (28, sourceBody255_234, 255, 43))

def sourceBody255_236 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_235 sourceBody255_4

def sourceBody255_237 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_236 sourceBody255_0

def sourceBody255_238 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_233 sourceBody255_237

def sourceBody255_239 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_170 sourceBody255_0

def sourceBody255_240 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_239 sourceBody255_0

def sourceBody255_241 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_238 sourceBody255_240

def sourceBody255_242 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 16)

def sourceBody255_243 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 12)

def sourceBody255_244 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody255_245 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody255_246 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.less) 20 (Flapjack.WordRegImm.reg 36) sourceBody255_244 sourceBody255_245

def sourceBody255_247 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_246 sourceBody255_4

def sourceBody255_248 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 20)

def sourceBody255_249 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.const 44#64)

def sourceBody255_250 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.longMul 6 6 20 36))

def sourceBody255_251 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 32, Flapjack.WordLangExpHOL.var 6])

def sourceBody255_252 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 24,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 16)
        (Flapjack.WordLangExpHOL.const 5#64)])

def sourceBody255_253 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody255_254 : WordLangProgHOL (BitVec 64) :=
.call (some (([28]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody255_0, 255, 44)) (some 253) ([22, 14]) (some (20, sourceBody255_253, 255, 45))

def sourceBody255_255 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_254 sourceBody255_4

def sourceBody255_256 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_255 sourceBody255_0

def sourceBody255_257 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_252 sourceBody255_256

def sourceBody255_258 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_251 sourceBody255_257

def sourceBody255_259 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_250 sourceBody255_258

def sourceBody255_260 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_249 sourceBody255_259

def sourceBody255_261 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_242 sourceBody255_260

def sourceBody255_262 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_0 sourceBody255_261

def sourceBody255_263 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_0 sourceBody255_262

def sourceBody255_264 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 16, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody255_265 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 28)

def sourceBody255_266 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_265 sourceBody255_0

def sourceBody255_267 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_266 sourceBody255_0

def sourceBody255_268 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_264 sourceBody255_267

def sourceBody255_269 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_0 sourceBody255_268

def sourceBody255_270 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_263 sourceBody255_269

def sourceBody255_271 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_270 sourceBody255_197

def sourceBody255_272 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.WordRegImm.imm 0#64) sourceBody255_271 sourceBody255_199

def sourceBody255_273 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_272 sourceBody255_4

def sourceBody255_274 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_273 sourceBody255_0

def sourceBody255_275 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_248 sourceBody255_274

def sourceBody255_276 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_247 sourceBody255_275

def sourceBody255_277 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_243 sourceBody255_276

def sourceBody255_278 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_242 sourceBody255_277

def sourceBody255_279 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
  PUnit.unit Flapjack.Spt.ln) sourceBody255_278 (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
    PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody255_280 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_279 sourceBody255_4

def sourceBody255_281 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_4 sourceBody255_280

def sourceBody255_282 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_241 sourceBody255_281

def sourceBody255_283 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 24)

def sourceBody255_284 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 12)

def sourceBody255_285 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 26, Flapjack.WordLangExpHOL.const 448#64])

def sourceBody255_286 : WordLangProgHOL (BitVec 64) :=
.call (some (([28]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
      PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody255_0, 255, 46)) (some 238) ([20, 36, 6, 22]) (some (20, sourceBody255_253, 255, 47))

def sourceBody255_287 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_286 sourceBody255_4

def sourceBody255_288 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_287 sourceBody255_0

def sourceBody255_289 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_285 sourceBody255_288

def sourceBody255_290 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_284 sourceBody255_289

def sourceBody255_291 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_243 sourceBody255_290

def sourceBody255_292 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_283 sourceBody255_291

def sourceBody255_293 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_0 sourceBody255_292

def sourceBody255_294 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_0 sourceBody255_293

def sourceBody255_295 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_282 sourceBody255_294

def sourceBody255_296 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 8)

def sourceBody255_297 : WordLangProgHOL (BitVec 64) :=
.call (some (([28]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
      PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody255_0, 255, 48)) (some 70) ([20]) (some (20, sourceBody255_253, 255, 49))

def sourceBody255_298 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_297 sourceBody255_4

def sourceBody255_299 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_298 sourceBody255_0

def sourceBody255_300 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_296 sourceBody255_299

def sourceBody255_301 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_0 sourceBody255_300

def sourceBody255_302 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_0 sourceBody255_301

def sourceBody255_303 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_295 sourceBody255_302

def sourceBody255_304 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 30, Flapjack.WordLangExpHOL.const 512#64])

def sourceBody255_305 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 26, Flapjack.WordLangExpHOL.const 480#64])

def sourceBody255_306 : WordLangProgHOL (BitVec 64) :=
.call (some (([28]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
      PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody255_0, 255, 50)) (some 244) ([20, 36]) (some (20, sourceBody255_253, 255, 51))

def sourceBody255_307 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_306 sourceBody255_4

def sourceBody255_308 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_307 sourceBody255_0

def sourceBody255_309 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_305 sourceBody255_308

def sourceBody255_310 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_304 sourceBody255_309

def sourceBody255_311 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_0 sourceBody255_310

def sourceBody255_312 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_0 sourceBody255_311

def sourceBody255_313 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_303 sourceBody255_312

def sourceBody255_314 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 30, Flapjack.WordLangExpHOL.const 520#64])

def sourceBody255_315 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 26, Flapjack.WordLangExpHOL.const 512#64])

def sourceBody255_316 : WordLangProgHOL (BitVec 64) :=
.call (some (([28]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
      PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody255_0, 255, 52)) (some 244) ([20, 36]) (some (20, sourceBody255_253, 255, 53))

def sourceBody255_317 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_316 sourceBody255_4

def sourceBody255_318 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_317 sourceBody255_0

def sourceBody255_319 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_315 sourceBody255_318

def sourceBody255_320 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_314 sourceBody255_319

def sourceBody255_321 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_0 sourceBody255_320

def sourceBody255_322 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_0 sourceBody255_321

def sourceBody255_323 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_313 sourceBody255_322

def sourceBody255_324 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 64#64]))

def sourceBody255_325 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 72#64]))

def sourceBody255_326 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 26, Flapjack.WordLangExpHOL.const 544#64])

def sourceBody255_327 : WordLangProgHOL (BitVec 64) :=
.call (some (([28]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
      (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody255_0, 255, 54)) (some 239) ([20, 36, 6]) (some (20, sourceBody255_253, 255, 55))

def sourceBody255_328 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_327 sourceBody255_4

def sourceBody255_329 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_328 sourceBody255_0

def sourceBody255_330 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_326 sourceBody255_329

def sourceBody255_331 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_325 sourceBody255_330

def sourceBody255_332 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_324 sourceBody255_331

def sourceBody255_333 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_0 sourceBody255_332

def sourceBody255_334 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_0 sourceBody255_333

def sourceBody255_335 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_323 sourceBody255_334

def sourceBody255_336 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 30, Flapjack.WordLangExpHOL.const 532#64])

def sourceBody255_337 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 26, Flapjack.WordLangExpHOL.const 576#64])

def sourceBody255_338 : WordLangProgHOL (BitVec 64) :=
.call (some (([28]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
      (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody255_0, 255, 56)) (some 244) ([20, 36]) (some (20, sourceBody255_253, 255, 57))

def sourceBody255_339 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_338 sourceBody255_4

def sourceBody255_340 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_339 sourceBody255_0

def sourceBody255_341 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_337 sourceBody255_340

def sourceBody255_342 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_336 sourceBody255_341

def sourceBody255_343 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_0 sourceBody255_342

def sourceBody255_344 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_0 sourceBody255_343

def sourceBody255_345 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_335 sourceBody255_344

def sourceBody255_346 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 26)

def sourceBody255_347 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.const 19#64)

def sourceBody255_348 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 4)

def sourceBody255_349 : WordLangProgHOL (BitVec 64) :=
.call (some (([28]), ((Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody255_0, 255, 58)) (some 240) ([20, 36, 6]) (some (20, sourceBody255_253, 255, 59))

def sourceBody255_350 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_349 sourceBody255_4

def sourceBody255_351 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_350 sourceBody255_0

def sourceBody255_352 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_348 sourceBody255_351

def sourceBody255_353 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_347 sourceBody255_352

def sourceBody255_354 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_346 sourceBody255_353

def sourceBody255_355 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_0 sourceBody255_354

def sourceBody255_356 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_0 sourceBody255_355

def sourceBody255_357 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_345 sourceBody255_356

def sourceBody255_358 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 10)

def sourceBody255_359 : WordLangProgHOL (BitVec 64) :=
.call (some (([28]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody255_0, 255, 60)) (some 70) ([20]) (some (20, sourceBody255_253, 255, 61))

def sourceBody255_360 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_359 sourceBody255_4

def sourceBody255_361 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_360 sourceBody255_0

def sourceBody255_362 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_358 sourceBody255_361

def sourceBody255_363 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_0 sourceBody255_362

def sourceBody255_364 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_0 sourceBody255_363

def sourceBody255_365 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_357 sourceBody255_364

def sourceBody255_366 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody255_367 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [28]

def sourceBody255_368 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_367 sourceBody255_0

def sourceBody255_369 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_366 sourceBody255_368

def sourceBody255_370 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_365 sourceBody255_369

def sourceBody255_371 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_232 sourceBody255_370

def sourceBody255_372 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_0 sourceBody255_371

def sourceBody255_373 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_231 sourceBody255_372

def sourceBody255_374 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_0 sourceBody255_373

def sourceBody255_375 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_230 sourceBody255_374

def sourceBody255_376 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_170 sourceBody255_375

def sourceBody255_377 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_0 sourceBody255_376

def sourceBody255_378 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_169 sourceBody255_377

def sourceBody255_379 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_0 sourceBody255_378

def sourceBody255_380 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_0 sourceBody255_379

def sourceBody255_381 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_163 sourceBody255_380

def sourceBody255_382 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_0 sourceBody255_381

def sourceBody255_383 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_0 sourceBody255_382

def sourceBody255_384 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_159 sourceBody255_383

def sourceBody255_385 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_0 sourceBody255_384

def sourceBody255_386 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_158 sourceBody255_385

def sourceBody255_387 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_0 sourceBody255_386

def sourceBody255_388 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_157 sourceBody255_387

def sourceBody255_389 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_12 sourceBody255_388

def sourceBody255_390 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_0 sourceBody255_389

def sourceBody255_391 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_0 sourceBody255_390

def sourceBody255_392 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_6 sourceBody255_391

def sourceBody255_393 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_0 sourceBody255_392

def sourceBody255_394 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_0 sourceBody255_393

def sourceBody255_395 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_1 sourceBody255_394

def sourceBody255_396 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody255_0 sourceBody255_395

def source255 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (255, 3, sourceBody255_396)
end InitECandidate.Proofs.WordStages
