import InitECandidate.Proofs.WordStages.Source347
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody363_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody363_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 2)

def sourceBody363_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 24

def sourceBody363_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody363_0, 363, 2)) (some 362) ([24]) (some (24, sourceBody363_2, 363, 3))

def sourceBody363_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody363_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_3 sourceBody363_4

def sourceBody363_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_5 sourceBody363_0

def sourceBody363_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_1 sourceBody363_6

def sourceBody363_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 12)

def sourceBody363_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody363_10 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody363_0, 363, 4)) (some 68) ([18]) (some (18, sourceBody363_9, 363, 5))

def sourceBody363_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_10 sourceBody363_4

def sourceBody363_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_11 sourceBody363_0

def sourceBody363_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_8 sourceBody363_12

def sourceBody363_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 24, Flapjack.WordLangExpHOL.const 10#64])

def sourceBody363_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 18)

def sourceBody363_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 0#64]))

def sourceBody363_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 10)

def sourceBody363_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody363_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody363_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody363_21 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 28 (Flapjack.WordRegImm.reg 14) sourceBody363_19 sourceBody363_20

def sourceBody363_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_21 sourceBody363_4

def sourceBody363_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 28)

def sourceBody363_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 30)

def sourceBody363_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody363_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody363_27 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody363_0, 363, 6)) (some 177) ([16, 28]) (some (16, sourceBody363_26, 363, 7))

def sourceBody363_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_27 sourceBody363_4

def sourceBody363_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_28 sourceBody363_0

def sourceBody363_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_25 sourceBody363_29

def sourceBody363_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_24 sourceBody363_30

def sourceBody363_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 30, Flapjack.WordLangExpHOL.var 22])

def sourceBody363_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 16)

def sourceBody363_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_33 sourceBody363_0

def sourceBody363_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_34 sourceBody363_0

def sourceBody363_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_32 sourceBody363_35

def sourceBody363_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_0 sourceBody363_36

def sourceBody363_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_31 sourceBody363_37

def sourceBody363_39 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 26 (Flapjack.WordRegImm.imm 0#64) sourceBody363_38 sourceBody363_0

def sourceBody363_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_39 sourceBody363_4

def sourceBody363_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_40 sourceBody363_0

def sourceBody363_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_23 sourceBody363_41

def sourceBody363_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_22 sourceBody363_42

def sourceBody363_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_18 sourceBody363_43

def sourceBody363_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_17 sourceBody363_44

def sourceBody363_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody363_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 16#64],
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody363_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 16#64],
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody363_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 16#64],
        Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody363_50 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody363_0, 363, 8)) (some 353) ([16, 28, 14, 26, 20]) (some (16, sourceBody363_26, 363, 9))

def sourceBody363_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_50 sourceBody363_4

def sourceBody363_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_51 sourceBody363_0

def sourceBody363_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_49 sourceBody363_52

def sourceBody363_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_48 sourceBody363_53

def sourceBody363_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_47 sourceBody363_54

def sourceBody363_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_46 sourceBody363_55

def sourceBody363_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_24 sourceBody363_56

def sourceBody363_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_45 sourceBody363_57

def sourceBody363_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_58 sourceBody363_37

def sourceBody363_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 10)

def sourceBody363_61 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notLower) 28 (Flapjack.WordRegImm.reg 14) sourceBody363_19 sourceBody363_20

def sourceBody363_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_61 sourceBody363_4

def sourceBody363_63 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 48#64]))

def sourceBody363_64 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 48#64],
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody363_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 48#64],
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody363_66 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 48#64],
        Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody363_67 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody363_0, 363, 10)) (some 353) ([16, 28, 14, 26, 20]) (some (16, sourceBody363_26, 363, 11))

def sourceBody363_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_67 sourceBody363_4

def sourceBody363_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_68 sourceBody363_0

def sourceBody363_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_66 sourceBody363_69

def sourceBody363_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_65 sourceBody363_70

def sourceBody363_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_64 sourceBody363_71

def sourceBody363_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_63 sourceBody363_72

def sourceBody363_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_24 sourceBody363_73

def sourceBody363_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_74 sourceBody363_37

def sourceBody363_76 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 80#64]))

def sourceBody363_77 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 80#64],
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody363_78 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 80#64],
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody363_79 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 80#64],
        Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody363_80 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody363_0, 363, 12)) (some 353) ([16, 28, 14, 26, 20]) (some (16, sourceBody363_26, 363, 13))

def sourceBody363_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_80 sourceBody363_4

def sourceBody363_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_81 sourceBody363_0

def sourceBody363_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_79 sourceBody363_82

def sourceBody363_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_78 sourceBody363_83

def sourceBody363_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_77 sourceBody363_84

def sourceBody363_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_76 sourceBody363_85

def sourceBody363_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_24 sourceBody363_86

def sourceBody363_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_87 sourceBody363_37

def sourceBody363_89 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 112#64]))

def sourceBody363_90 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 112#64],
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody363_91 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 112#64],
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody363_92 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 112#64],
        Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody363_93 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody363_0, 363, 14)) (some 353) ([16, 28, 14, 26, 20]) (some (16, sourceBody363_26, 363, 15))

def sourceBody363_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_93 sourceBody363_4

def sourceBody363_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_94 sourceBody363_0

def sourceBody363_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_92 sourceBody363_95

def sourceBody363_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_91 sourceBody363_96

def sourceBody363_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_90 sourceBody363_97

def sourceBody363_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_89 sourceBody363_98

def sourceBody363_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_24 sourceBody363_99

def sourceBody363_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_88 sourceBody363_100

def sourceBody363_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_101 sourceBody363_37

def sourceBody363_103 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 26 (Flapjack.WordRegImm.imm 0#64) sourceBody363_75 sourceBody363_102

def sourceBody363_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_103 sourceBody363_4

def sourceBody363_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_104 sourceBody363_0

def sourceBody363_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_23 sourceBody363_105

def sourceBody363_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_62 sourceBody363_106

def sourceBody363_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_60 sourceBody363_107

def sourceBody363_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_19 sourceBody363_108

def sourceBody363_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_59 sourceBody363_109

def sourceBody363_111 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 144#64]))

def sourceBody363_112 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody363_0, 363, 16)) (some 177) ([16, 28]) (some (16, sourceBody363_26, 363, 17))

def sourceBody363_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_112 sourceBody363_4

def sourceBody363_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_113 sourceBody363_0

def sourceBody363_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_111 sourceBody363_114

def sourceBody363_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_24 sourceBody363_115

def sourceBody363_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_110 sourceBody363_116

def sourceBody363_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_117 sourceBody363_37

def sourceBody363_119 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 152#64]))

def sourceBody363_120 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody363_0, 363, 18)) (some 355) ([16, 28]) (some (16, sourceBody363_26, 363, 19))

def sourceBody363_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_120 sourceBody363_4

def sourceBody363_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_121 sourceBody363_0

def sourceBody363_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_119 sourceBody363_122

def sourceBody363_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_24 sourceBody363_123

def sourceBody363_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_118 sourceBody363_124

def sourceBody363_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_125 sourceBody363_37

def sourceBody363_127 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 160#64]))

def sourceBody363_128 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 160#64],
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody363_129 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 160#64],
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody363_130 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 160#64],
        Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody363_131 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody363_0, 363, 20)) (some 353) ([16, 28, 14, 26, 20]) (some (16, sourceBody363_26, 363, 21))

def sourceBody363_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_131 sourceBody363_4

def sourceBody363_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_132 sourceBody363_0

def sourceBody363_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_130 sourceBody363_133

def sourceBody363_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_129 sourceBody363_134

def sourceBody363_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_128 sourceBody363_135

def sourceBody363_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_127 sourceBody363_136

def sourceBody363_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_24 sourceBody363_137

def sourceBody363_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_126 sourceBody363_138

def sourceBody363_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_139 sourceBody363_37

def sourceBody363_141 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 192#64]))

def sourceBody363_142 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 200#64]))

def sourceBody363_143 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody363_0, 363, 22)) (some 176) ([16, 28, 14]) (some (16, sourceBody363_26, 363, 23))

def sourceBody363_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_143 sourceBody363_4

def sourceBody363_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_144 sourceBody363_0

def sourceBody363_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_142 sourceBody363_145

def sourceBody363_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_141 sourceBody363_146

def sourceBody363_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_24 sourceBody363_147

def sourceBody363_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_140 sourceBody363_148

def sourceBody363_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_149 sourceBody363_37

def sourceBody363_151 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 208#64]))

def sourceBody363_152 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 216#64]))

def sourceBody363_153 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody363_0, 363, 24)) (some 357) ([16, 28, 14]) (some (16, sourceBody363_26, 363, 25))

def sourceBody363_154 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_153 sourceBody363_4

def sourceBody363_155 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_154 sourceBody363_0

def sourceBody363_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_152 sourceBody363_155

def sourceBody363_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_151 sourceBody363_156

def sourceBody363_158 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_24 sourceBody363_157

def sourceBody363_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_158 sourceBody363_37

def sourceBody363_160 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 26 (Flapjack.WordRegImm.imm 0#64) sourceBody363_159 sourceBody363_0

def sourceBody363_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_160 sourceBody363_4

def sourceBody363_162 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_161 sourceBody363_0

def sourceBody363_163 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_23 sourceBody363_162

def sourceBody363_164 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_22 sourceBody363_163

def sourceBody363_165 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_18 sourceBody363_164

def sourceBody363_166 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_17 sourceBody363_165

def sourceBody363_167 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_150 sourceBody363_166

def sourceBody363_168 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 3#64)

def sourceBody363_169 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 28 (Flapjack.WordRegImm.reg 14) sourceBody363_19 sourceBody363_20

def sourceBody363_170 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_169 sourceBody363_4

def sourceBody363_171 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 224#64]))

def sourceBody363_172 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 224#64],
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody363_173 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 224#64],
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody363_174 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 224#64],
        Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody363_175 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody363_0, 363, 26)) (some 353) ([16, 28, 14, 26, 20]) (some (16, sourceBody363_26, 363, 27))

def sourceBody363_176 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_175 sourceBody363_4

def sourceBody363_177 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_176 sourceBody363_0

def sourceBody363_178 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_174 sourceBody363_177

def sourceBody363_179 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_173 sourceBody363_178

def sourceBody363_180 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_172 sourceBody363_179

def sourceBody363_181 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_171 sourceBody363_180

def sourceBody363_182 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_24 sourceBody363_181

def sourceBody363_183 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_182 sourceBody363_37

def sourceBody363_184 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 256#64]))

def sourceBody363_185 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 264#64]))

def sourceBody363_186 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody363_0, 363, 28)) (some 358) ([16, 28, 14]) (some (16, sourceBody363_26, 363, 29))

def sourceBody363_187 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_186 sourceBody363_4

def sourceBody363_188 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_187 sourceBody363_0

def sourceBody363_189 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_185 sourceBody363_188

def sourceBody363_190 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_184 sourceBody363_189

def sourceBody363_191 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_24 sourceBody363_190

def sourceBody363_192 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_183 sourceBody363_191

def sourceBody363_193 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_192 sourceBody363_37

def sourceBody363_194 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 26 (Flapjack.WordRegImm.imm 0#64) sourceBody363_193 sourceBody363_0

def sourceBody363_195 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_194 sourceBody363_4

def sourceBody363_196 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_195 sourceBody363_0

def sourceBody363_197 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_23 sourceBody363_196

def sourceBody363_198 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_170 sourceBody363_197

def sourceBody363_199 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_168 sourceBody363_198

def sourceBody363_200 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_17 sourceBody363_199

def sourceBody363_201 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_167 sourceBody363_200

def sourceBody363_202 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 4#64)

def sourceBody363_203 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 272#64]))

def sourceBody363_204 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 280#64]))

def sourceBody363_205 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody363_0, 363, 30)) (some 361) ([16, 28, 14]) (some (16, sourceBody363_26, 363, 31))

def sourceBody363_206 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_205 sourceBody363_4

def sourceBody363_207 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_206 sourceBody363_0

def sourceBody363_208 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_204 sourceBody363_207

def sourceBody363_209 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_203 sourceBody363_208

def sourceBody363_210 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_24 sourceBody363_209

def sourceBody363_211 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_210 sourceBody363_37

def sourceBody363_212 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 26 (Flapjack.WordRegImm.imm 0#64) sourceBody363_211 sourceBody363_0

def sourceBody363_213 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_212 sourceBody363_4

def sourceBody363_214 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_213 sourceBody363_0

def sourceBody363_215 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_23 sourceBody363_214

def sourceBody363_216 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_170 sourceBody363_215

def sourceBody363_217 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_202 sourceBody363_216

def sourceBody363_218 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_17 sourceBody363_217

def sourceBody363_219 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_201 sourceBody363_218

def sourceBody363_220 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 4)

def sourceBody363_221 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 288#64]))

def sourceBody363_222 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 288#64],
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody363_223 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 288#64],
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody363_224 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 288#64],
        Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody363_225 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody363_0, 363, 32)) (some 353) ([16, 28, 14, 26, 20]) (some (16, sourceBody363_26, 363, 33))

def sourceBody363_226 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_225 sourceBody363_4

def sourceBody363_227 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_226 sourceBody363_0

def sourceBody363_228 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_224 sourceBody363_227

def sourceBody363_229 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_223 sourceBody363_228

def sourceBody363_230 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_222 sourceBody363_229

def sourceBody363_231 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_221 sourceBody363_230

def sourceBody363_232 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_24 sourceBody363_231

def sourceBody363_233 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_232 sourceBody363_37

def sourceBody363_234 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 320#64]))

def sourceBody363_235 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 320#64],
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody363_236 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 320#64],
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody363_237 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 320#64],
        Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody363_238 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody363_0, 363, 34)) (some 353) ([16, 28, 14, 26, 20]) (some (16, sourceBody363_26, 363, 35))

def sourceBody363_239 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_238 sourceBody363_4

def sourceBody363_240 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_239 sourceBody363_0

def sourceBody363_241 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_237 sourceBody363_240

def sourceBody363_242 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_236 sourceBody363_241

def sourceBody363_243 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_235 sourceBody363_242

def sourceBody363_244 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_234 sourceBody363_243

def sourceBody363_245 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_24 sourceBody363_244

def sourceBody363_246 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_233 sourceBody363_245

def sourceBody363_247 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_246 sourceBody363_37

def sourceBody363_248 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 352#64]))

def sourceBody363_249 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 352#64],
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody363_250 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 352#64],
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody363_251 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 352#64],
        Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody363_252 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody363_0, 363, 36)) (some 353) ([16, 28, 14, 26, 20]) (some (16, sourceBody363_26, 363, 37))

def sourceBody363_253 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_252 sourceBody363_4

def sourceBody363_254 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_253 sourceBody363_0

def sourceBody363_255 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_251 sourceBody363_254

def sourceBody363_256 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_250 sourceBody363_255

def sourceBody363_257 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_249 sourceBody363_256

def sourceBody363_258 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_248 sourceBody363_257

def sourceBody363_259 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_24 sourceBody363_258

def sourceBody363_260 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_247 sourceBody363_259

def sourceBody363_261 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_260 sourceBody363_37

def sourceBody363_262 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 26 (Flapjack.WordRegImm.imm 0#64) sourceBody363_261 sourceBody363_0

def sourceBody363_263 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_262 sourceBody363_4

def sourceBody363_264 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_263 sourceBody363_0

def sourceBody363_265 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_23 sourceBody363_264

def sourceBody363_266 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_170 sourceBody363_265

def sourceBody363_267 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_18 sourceBody363_266

def sourceBody363_268 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_220 sourceBody363_267

def sourceBody363_269 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_219 sourceBody363_268

def sourceBody363_270 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 2#64)

def sourceBody363_271 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 6)

def sourceBody363_272 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody363_0, 363, 38)) (some 177) ([16, 28]) (some (16, sourceBody363_26, 363, 39))

def sourceBody363_273 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_272 sourceBody363_4

def sourceBody363_274 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_273 sourceBody363_0

def sourceBody363_275 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_271 sourceBody363_274

def sourceBody363_276 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_24 sourceBody363_275

def sourceBody363_277 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_276 sourceBody363_37

def sourceBody363_278 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 128#64)

def sourceBody363_279 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.store8 28 (Flapjack.WordLangAddr.addr 16 0#64))

def sourceBody363_280 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_279 sourceBody363_0

def sourceBody363_281 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_278 sourceBody363_280

def sourceBody363_282 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_24 sourceBody363_281

def sourceBody363_283 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_277 sourceBody363_282

def sourceBody363_284 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 30, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody363_285 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_284 sourceBody363_281

def sourceBody363_286 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_283 sourceBody363_285

def sourceBody363_287 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 30, Flapjack.WordLangExpHOL.const 2#64])

def sourceBody363_288 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_287 sourceBody363_35

def sourceBody363_289 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_0 sourceBody363_288

def sourceBody363_290 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_286 sourceBody363_289

def sourceBody363_291 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 26 (Flapjack.WordRegImm.imm 0#64) sourceBody363_290 sourceBody363_0

def sourceBody363_292 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_291 sourceBody363_4

def sourceBody363_293 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_292 sourceBody363_0

def sourceBody363_294 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_23 sourceBody363_293

def sourceBody363_295 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_170 sourceBody363_294

def sourceBody363_296 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_270 sourceBody363_295

def sourceBody363_297 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_220 sourceBody363_296

def sourceBody363_298 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_269 sourceBody363_297

def sourceBody363_299 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 30, Flapjack.WordLangExpHOL.var 18])

def sourceBody363_300 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 16)

def sourceBody363_301 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody363_302 : WordLangProgHOL (BitVec 64) :=
.call (some (([28]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody363_0, 363, 40)) (some 180) ([14]) (some (14, sourceBody363_301, 363, 41))

def sourceBody363_303 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_302 sourceBody363_4

def sourceBody363_304 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_303 sourceBody363_0

def sourceBody363_305 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_300 sourceBody363_304

def sourceBody363_306 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.var 28])

def sourceBody363_307 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 14)

def sourceBody363_308 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 16)

def sourceBody363_309 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody363_310 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)
        (Flapjack.Spt.ls PUnit.unit))
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody363_0, 363, 42)) (some 178) ([20, 32]) (some (20, sourceBody363_309, 363, 43))

def sourceBody363_311 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_310 sourceBody363_4

def sourceBody363_312 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_311 sourceBody363_0

def sourceBody363_313 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_308 sourceBody363_312

def sourceBody363_314 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_307 sourceBody363_313

def sourceBody363_315 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_0 sourceBody363_314

def sourceBody363_316 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_0 sourceBody363_315

def sourceBody363_317 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 10)

def sourceBody363_318 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody363_319 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody363_320 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody363_321 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 20 (Flapjack.WordRegImm.reg 32) sourceBody363_319 sourceBody363_320

def sourceBody363_322 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_321 sourceBody363_4

def sourceBody363_323 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 20)

def sourceBody363_324 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody363_325 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 26)

def sourceBody363_326 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_325 sourceBody363_0

def sourceBody363_327 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_326 sourceBody363_0

def sourceBody363_328 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_324 sourceBody363_327

def sourceBody363_329 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_0 sourceBody363_328

def sourceBody363_330 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 14)

def sourceBody363_331 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.store8 20 (Flapjack.WordLangAddr.addr 26 0#64))

def sourceBody363_332 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_331 sourceBody363_0

def sourceBody363_333 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_317 sourceBody363_332

def sourceBody363_334 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_330 sourceBody363_333

def sourceBody363_335 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_329 sourceBody363_334

def sourceBody363_336 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.WordRegImm.imm 0#64) sourceBody363_335 sourceBody363_0

def sourceBody363_337 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_336 sourceBody363_4

def sourceBody363_338 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_337 sourceBody363_0

def sourceBody363_339 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_323 sourceBody363_338

def sourceBody363_340 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_322 sourceBody363_339

def sourceBody363_341 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_318 sourceBody363_340

def sourceBody363_342 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_317 sourceBody363_341

def sourceBody363_343 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_316 sourceBody363_342

def sourceBody363_344 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 30, Flapjack.WordLangExpHOL.var 14])

def sourceBody363_345 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [26, 20]

def sourceBody363_346 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_345 sourceBody363_0

def sourceBody363_347 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_344 sourceBody363_346

def sourceBody363_348 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_330 sourceBody363_347

def sourceBody363_349 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_343 sourceBody363_348

def sourceBody363_350 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_306 sourceBody363_349

def sourceBody363_351 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_0 sourceBody363_350

def sourceBody363_352 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_305 sourceBody363_351

def sourceBody363_353 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_0 sourceBody363_352

def sourceBody363_354 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_0 sourceBody363_353

def sourceBody363_355 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_299 sourceBody363_354

def sourceBody363_356 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_0 sourceBody363_355

def sourceBody363_357 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_298 sourceBody363_356

def sourceBody363_358 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_0 sourceBody363_357

def sourceBody363_359 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_0 sourceBody363_358

def sourceBody363_360 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_16 sourceBody363_359

def sourceBody363_361 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_0 sourceBody363_360

def sourceBody363_362 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_15 sourceBody363_361

def sourceBody363_363 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_0 sourceBody363_362

def sourceBody363_364 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_14 sourceBody363_363

def sourceBody363_365 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_0 sourceBody363_364

def sourceBody363_366 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_13 sourceBody363_365

def sourceBody363_367 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_0 sourceBody363_366

def sourceBody363_368 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_0 sourceBody363_367

def sourceBody363_369 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_7 sourceBody363_368

def sourceBody363_370 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_0 sourceBody363_369

def sourceBody363_371 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody363_0 sourceBody363_370

def source363 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (363, 4, sourceBody363_371)
end InitECandidate.Proofs.WordStages
