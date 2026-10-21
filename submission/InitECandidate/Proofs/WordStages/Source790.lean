import InitECandidate.Proofs.WordStages.Source774
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody790_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody790_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 4)

def sourceBody790_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 50

def sourceBody790_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody790_0, 790, 2)) (some 763) ([50]) (some (50, sourceBody790_2, 790, 3))

def sourceBody790_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody790_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_3 sourceBody790_4

def sourceBody790_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_5 sourceBody790_0

def sourceBody790_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_1 sourceBody790_6

def sourceBody790_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 16)

def sourceBody790_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 66 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody790_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody790_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody790_12 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 34 (Flapjack.WordRegImm.reg 66) sourceBody790_10 sourceBody790_11

def sourceBody790_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_12 sourceBody790_4

def sourceBody790_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 34)

def sourceBody790_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody790_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [50]

def sourceBody790_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_16 sourceBody790_0

def sourceBody790_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_15 sourceBody790_17

def sourceBody790_19 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.imm 0#64) sourceBody790_18 sourceBody790_0

def sourceBody790_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_19 sourceBody790_4

def sourceBody790_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_20 sourceBody790_0

def sourceBody790_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_14 sourceBody790_21

def sourceBody790_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_13 sourceBody790_22

def sourceBody790_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_9 sourceBody790_23

def sourceBody790_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_8 sourceBody790_24

def sourceBody790_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 6)

def sourceBody790_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 34

def sourceBody790_28 : WordLangProgHOL (BitVec 64) :=
.call (some (([50]), ((Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody790_0, 790, 4)) (some 775) ([34]) (some (34, sourceBody790_27, 790, 5))

def sourceBody790_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_28 sourceBody790_4

def sourceBody790_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_29 sourceBody790_0

def sourceBody790_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_26 sourceBody790_30

def sourceBody790_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 66 (Flapjack.WordLangExpHOL.var 50)

def sourceBody790_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody790_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 66 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody790_35 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 66 (Flapjack.WordRegImm.reg 12) sourceBody790_9 sourceBody790_34

def sourceBody790_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_35 sourceBody790_4

def sourceBody790_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 66)

def sourceBody790_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [34]

def sourceBody790_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_38 sourceBody790_0

def sourceBody790_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_11 sourceBody790_39

def sourceBody790_41 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 46 (Flapjack.WordRegImm.imm 0#64) sourceBody790_40 sourceBody790_0

def sourceBody790_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_41 sourceBody790_4

def sourceBody790_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_42 sourceBody790_0

def sourceBody790_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_37 sourceBody790_43

def sourceBody790_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_36 sourceBody790_44

def sourceBody790_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_33 sourceBody790_45

def sourceBody790_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_32 sourceBody790_46

def sourceBody790_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 66

def sourceBody790_49 : WordLangProgHOL (BitVec 64) :=
.call (some (([34]), ((Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody790_0, 790, 6)) (some 69) ([]) (some (66, sourceBody790_48, 790, 7))

def sourceBody790_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_49 sourceBody790_4

def sourceBody790_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_50 sourceBody790_0

def sourceBody790_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 96#64)

def sourceBody790_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody790_54 : WordLangProgHOL (BitVec 64) :=
.call (some (([66]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody790_0, 790, 8)) (some 68) ([12]) (some (12, sourceBody790_53, 790, 9))

def sourceBody790_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_54 sourceBody790_4

def sourceBody790_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_55 sourceBody790_0

def sourceBody790_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_52 sourceBody790_56

def sourceBody790_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.const 192#64)

def sourceBody790_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 46

def sourceBody790_60 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
      PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody790_0, 790, 10)) (some 68) ([46]) (some (46, sourceBody790_59, 790, 11))

def sourceBody790_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_60 sourceBody790_4

def sourceBody790_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_61 sourceBody790_0

def sourceBody790_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_58 sourceBody790_62

def sourceBody790_64 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 576#64)

def sourceBody790_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 30

def sourceBody790_66 : WordLangProgHOL (BitVec 64) :=
.call (some (([46]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
      PUnit.unit (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody790_0, 790, 12)) (some 68) ([30]) (some (30, sourceBody790_65, 790, 13))

def sourceBody790_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_66 sourceBody790_4

def sourceBody790_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_67 sourceBody790_0

def sourceBody790_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_64 sourceBody790_68

def sourceBody790_70 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 62 (Flapjack.WordLangExpHOL.var 66)

def sourceBody790_71 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 4)

def sourceBody790_72 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 62

def sourceBody790_73 : WordLangProgHOL (BitVec 64) :=
.call (some (([30]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
        PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
      PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody790_0, 790, 14)) (some 769) ([62, 22]) (some (62, sourceBody790_72, 790, 15))

def sourceBody790_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_73 sourceBody790_4

def sourceBody790_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_74 sourceBody790_0

def sourceBody790_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_71 sourceBody790_75

def sourceBody790_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_70 sourceBody790_76

def sourceBody790_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_0 sourceBody790_77

def sourceBody790_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_0 sourceBody790_78

def sourceBody790_80 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 62 (Flapjack.WordLangExpHOL.var 12)

def sourceBody790_81 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 6)

def sourceBody790_82 : WordLangProgHOL (BitVec 64) :=
.call (some (([30]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
        (Flapjack.Spt.bn Flapjack.Spt.ln
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
      PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody790_0, 790, 16)) (some 781) ([62, 22]) (some (62, sourceBody790_72, 790, 17))

def sourceBody790_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_82 sourceBody790_4

def sourceBody790_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_83 sourceBody790_0

def sourceBody790_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_81 sourceBody790_84

def sourceBody790_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_80 sourceBody790_85

def sourceBody790_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_0 sourceBody790_86

def sourceBody790_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_0 sourceBody790_87

def sourceBody790_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_79 sourceBody790_88

def sourceBody790_90 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.load (Flapjack.WordLangExpHOL.var 66))

def sourceBody790_91 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 62
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 66, Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody790_92 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 66, Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody790_93 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 66, Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody790_94 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 66, Flapjack.WordLangExpHOL.const 32#64]))

def sourceBody790_95 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 70
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 66, Flapjack.WordLangExpHOL.const 40#64]))

def sourceBody790_96 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 66, Flapjack.WordLangExpHOL.const 48#64]))

def sourceBody790_97 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 66, Flapjack.WordLangExpHOL.const 48#64],
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody790_98 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 66, Flapjack.WordLangExpHOL.const 48#64],
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody790_99 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 60
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 66, Flapjack.WordLangExpHOL.const 48#64],
        Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody790_100 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 66, Flapjack.WordLangExpHOL.const 48#64],
        Flapjack.WordLangExpHOL.const 32#64]))

def sourceBody790_101 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 66, Flapjack.WordLangExpHOL.const 48#64],
        Flapjack.WordLangExpHOL.const 40#64]))

def sourceBody790_102 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 68 (Flapjack.WordLangExpHOL.var 46)

def sourceBody790_103 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 30)

def sourceBody790_104 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 62)

def sourceBody790_105 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 22)

def sourceBody790_106 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 64 (Flapjack.WordLangExpHOL.var 54)

def sourceBody790_107 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 38)

def sourceBody790_108 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.var 70)

def sourceBody790_109 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 10)

def sourceBody790_110 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 72 (Flapjack.WordLangExpHOL.var 44)

def sourceBody790_111 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 28)

def sourceBody790_112 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 60)

def sourceBody790_113 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 20)

def sourceBody790_114 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.var 52)

def sourceBody790_115 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 12)

def sourceBody790_116 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 68

def sourceBody790_117 : WordLangProgHOL (BitVec 64) :=
.call (some (([36]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody790_0, 790, 18)) (some 789) ([68, 14, 48, 32, 64, 24, 56, 40, 72, 8, 42, 26, 58, 18]) (some (68, sourceBody790_116, 790, 19))

def sourceBody790_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_117 sourceBody790_4

def sourceBody790_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_118 sourceBody790_0

def sourceBody790_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_115 sourceBody790_119

def sourceBody790_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_114 sourceBody790_120

def sourceBody790_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_113 sourceBody790_121

def sourceBody790_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_112 sourceBody790_122

def sourceBody790_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_111 sourceBody790_123

def sourceBody790_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_110 sourceBody790_124

def sourceBody790_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_109 sourceBody790_125

def sourceBody790_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_108 sourceBody790_126

def sourceBody790_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_107 sourceBody790_127

def sourceBody790_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_106 sourceBody790_128

def sourceBody790_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_105 sourceBody790_129

def sourceBody790_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_104 sourceBody790_130

def sourceBody790_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_103 sourceBody790_131

def sourceBody790_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_102 sourceBody790_132

def sourceBody790_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_0 sourceBody790_133

def sourceBody790_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_0 sourceBody790_134

def sourceBody790_136 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 68 (Flapjack.WordLangExpHOL.var 2)

def sourceBody790_137 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 2)

def sourceBody790_138 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 46)

def sourceBody790_139 : WordLangProgHOL (BitVec 64) :=
.call (some (([36]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody790_0, 790, 20)) (some 754) ([68, 14, 48]) (some (68, sourceBody790_116, 790, 21))

def sourceBody790_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_139 sourceBody790_4

def sourceBody790_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_140 sourceBody790_0

def sourceBody790_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_138 sourceBody790_141

def sourceBody790_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_137 sourceBody790_142

def sourceBody790_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_136 sourceBody790_143

def sourceBody790_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_0 sourceBody790_144

def sourceBody790_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_0 sourceBody790_145

def sourceBody790_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_135 sourceBody790_146

def sourceBody790_148 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 68 (Flapjack.WordLangExpHOL.var 34)

def sourceBody790_149 : WordLangProgHOL (BitVec 64) :=
.call (some (([36]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody790_0, 790, 22)) (some 70) ([68]) (some (68, sourceBody790_116, 790, 23))

def sourceBody790_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_149 sourceBody790_4

def sourceBody790_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_150 sourceBody790_0

def sourceBody790_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_148 sourceBody790_151

def sourceBody790_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_0 sourceBody790_152

def sourceBody790_154 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_0 sourceBody790_153

def sourceBody790_155 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_147 sourceBody790_154

def sourceBody790_156 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody790_157 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [36]

def sourceBody790_158 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_157 sourceBody790_0

def sourceBody790_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_156 sourceBody790_158

def sourceBody790_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_155 sourceBody790_159

def sourceBody790_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_101 sourceBody790_160

def sourceBody790_162 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_0 sourceBody790_161

def sourceBody790_163 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_100 sourceBody790_162

def sourceBody790_164 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_0 sourceBody790_163

def sourceBody790_165 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_99 sourceBody790_164

def sourceBody790_166 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_0 sourceBody790_165

def sourceBody790_167 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_98 sourceBody790_166

def sourceBody790_168 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_0 sourceBody790_167

def sourceBody790_169 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_97 sourceBody790_168

def sourceBody790_170 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_0 sourceBody790_169

def sourceBody790_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_96 sourceBody790_170

def sourceBody790_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_0 sourceBody790_171

def sourceBody790_173 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_95 sourceBody790_172

def sourceBody790_174 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_0 sourceBody790_173

def sourceBody790_175 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_94 sourceBody790_174

def sourceBody790_176 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_0 sourceBody790_175

def sourceBody790_177 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_93 sourceBody790_176

def sourceBody790_178 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_0 sourceBody790_177

def sourceBody790_179 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_92 sourceBody790_178

def sourceBody790_180 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_0 sourceBody790_179

def sourceBody790_181 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_91 sourceBody790_180

def sourceBody790_182 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_0 sourceBody790_181

def sourceBody790_183 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_90 sourceBody790_182

def sourceBody790_184 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_0 sourceBody790_183

def sourceBody790_185 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_89 sourceBody790_184

def sourceBody790_186 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_69 sourceBody790_185

def sourceBody790_187 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_0 sourceBody790_186

def sourceBody790_188 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_0 sourceBody790_187

def sourceBody790_189 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_63 sourceBody790_188

def sourceBody790_190 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_0 sourceBody790_189

def sourceBody790_191 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_0 sourceBody790_190

def sourceBody790_192 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_57 sourceBody790_191

def sourceBody790_193 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_0 sourceBody790_192

def sourceBody790_194 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_0 sourceBody790_193

def sourceBody790_195 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_51 sourceBody790_194

def sourceBody790_196 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_0 sourceBody790_195

def sourceBody790_197 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_0 sourceBody790_196

def sourceBody790_198 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_47 sourceBody790_197

def sourceBody790_199 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_31 sourceBody790_198

def sourceBody790_200 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_0 sourceBody790_199

def sourceBody790_201 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_0 sourceBody790_200

def sourceBody790_202 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_25 sourceBody790_201

def sourceBody790_203 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_7 sourceBody790_202

def sourceBody790_204 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_0 sourceBody790_203

def sourceBody790_205 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody790_0 sourceBody790_204

def source790 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (790, 4, sourceBody790_205)
end InitECandidate.Proofs.WordStages
