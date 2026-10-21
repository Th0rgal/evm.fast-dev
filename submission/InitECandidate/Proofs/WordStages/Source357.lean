import InitECandidate.Proofs.WordStages.Source341
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody357_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody357_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 4)

def sourceBody357_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 6)

def sourceBody357_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 32

def sourceBody357_4 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody357_0, 357, 2)) (some 356) ([32, 22]) (some (32, sourceBody357_3, 357, 3))

def sourceBody357_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody357_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_4 sourceBody357_5

def sourceBody357_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_6 sourceBody357_0

def sourceBody357_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_2 sourceBody357_7

def sourceBody357_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_1 sourceBody357_8

def sourceBody357_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 2)

def sourceBody357_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 12)

def sourceBody357_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 22

def sourceBody357_13 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody357_0, 357, 4)) (some 178) ([22, 42]) (some (22, sourceBody357_12, 357, 5))

def sourceBody357_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_13 sourceBody357_5

def sourceBody357_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_14 sourceBody357_0

def sourceBody357_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_11 sourceBody357_15

def sourceBody357_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_10 sourceBody357_16

def sourceBody357_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.var 32])

def sourceBody357_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody357_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 42)

def sourceBody357_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 6)

def sourceBody357_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody357_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody357_24 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 30 (Flapjack.WordRegImm.reg 20) sourceBody357_22 sourceBody357_23

def sourceBody357_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_24 sourceBody357_5

def sourceBody357_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 30)

def sourceBody357_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 42)

def sourceBody357_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 24#64)

def sourceBody357_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.longMul 20 20 10 30))

def sourceBody357_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_29 sourceBody357_0

def sourceBody357_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_28 sourceBody357_30

def sourceBody357_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_27 sourceBody357_31

def sourceBody357_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.var 20])

def sourceBody357_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 40, Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody357_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 16)

def sourceBody357_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 33#64)

def sourceBody357_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.longMul 46 46 36 26))

def sourceBody357_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_37 sourceBody357_0

def sourceBody357_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_36 sourceBody357_38

def sourceBody357_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_35 sourceBody357_39

def sourceBody357_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 46)

def sourceBody357_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 8)

def sourceBody357_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody357_44 : WordLangProgHOL (BitVec 64) :=
.call (some (([28]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody357_0, 357, 6)) (some 180) ([18]) (some (18, sourceBody357_43, 357, 7))

def sourceBody357_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_44 sourceBody357_5

def sourceBody357_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_45 sourceBody357_0

def sourceBody357_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_42 sourceBody357_46

def sourceBody357_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 22)

def sourceBody357_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.const 21#64, Flapjack.WordLangExpHOL.var 28, Flapjack.WordLangExpHOL.var 8])

def sourceBody357_50 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody357_0, 357, 8)) (some 178) ([18, 38]) (some (18, sourceBody357_43, 357, 9))

def sourceBody357_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_50 sourceBody357_5

def sourceBody357_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_51 sourceBody357_0

def sourceBody357_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_49 sourceBody357_52

def sourceBody357_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_48 sourceBody357_53

def sourceBody357_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 22, Flapjack.WordLangExpHOL.var 32])

def sourceBody357_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 18)

def sourceBody357_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_56 sourceBody357_0

def sourceBody357_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_57 sourceBody357_0

def sourceBody357_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_55 sourceBody357_58

def sourceBody357_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_0 sourceBody357_59

def sourceBody357_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_54 sourceBody357_60

def sourceBody357_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 40, Flapjack.WordLangExpHOL.const 0#64]))

def sourceBody357_63 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 20#64)

def sourceBody357_64 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody357_0, 357, 10)) (some 176) ([18, 38, 14]) (some (18, sourceBody357_43, 357, 11))

def sourceBody357_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_64 sourceBody357_5

def sourceBody357_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_65 sourceBody357_0

def sourceBody357_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_63 sourceBody357_66

def sourceBody357_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_62 sourceBody357_67

def sourceBody357_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_48 sourceBody357_68

def sourceBody357_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_61 sourceBody357_69

def sourceBody357_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_70 sourceBody357_60

def sourceBody357_72 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 8)

def sourceBody357_73 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody357_0, 357, 12)) (some 178) ([18, 38]) (some (18, sourceBody357_43, 357, 13))

def sourceBody357_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_73 sourceBody357_5

def sourceBody357_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_74 sourceBody357_0

def sourceBody357_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_72 sourceBody357_75

def sourceBody357_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_48 sourceBody357_76

def sourceBody357_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_71 sourceBody357_77

def sourceBody357_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_78 sourceBody357_60

def sourceBody357_80 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 40, Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody357_81 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody357_82 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 38)

def sourceBody357_83 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 16)

def sourceBody357_84 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody357_85 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody357_86 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 34 (Flapjack.WordRegImm.reg 24) sourceBody357_84 sourceBody357_85

def sourceBody357_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_86 sourceBody357_5

def sourceBody357_88 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 34)

def sourceBody357_89 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 22)

def sourceBody357_90 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 18,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 38)
        (Flapjack.WordLangExpHOL.const 5#64)])

def sourceBody357_91 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody357_92 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody357_93 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody357_0, 357, 14)) (some 176) ([14, 34, 24]) (some (14, sourceBody357_92, 357, 15))

def sourceBody357_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_93 sourceBody357_5

def sourceBody357_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_94 sourceBody357_0

def sourceBody357_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_91 sourceBody357_95

def sourceBody357_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_90 sourceBody357_96

def sourceBody357_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_89 sourceBody357_97

def sourceBody357_99 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 22, Flapjack.WordLangExpHOL.var 32])

def sourceBody357_100 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 14)

def sourceBody357_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_100 sourceBody357_0

def sourceBody357_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_101 sourceBody357_0

def sourceBody357_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_99 sourceBody357_102

def sourceBody357_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_0 sourceBody357_103

def sourceBody357_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_98 sourceBody357_104

def sourceBody357_106 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 38, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody357_107 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 14)

def sourceBody357_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_107 sourceBody357_0

def sourceBody357_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_108 sourceBody357_0

def sourceBody357_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_106 sourceBody357_109

def sourceBody357_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_0 sourceBody357_110

def sourceBody357_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_105 sourceBody357_111

def sourceBody357_113 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody357_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_112 sourceBody357_113

def sourceBody357_115 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody357_116 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 44 (Flapjack.WordRegImm.imm 0#64) sourceBody357_114 sourceBody357_115

def sourceBody357_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_116 sourceBody357_5

def sourceBody357_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_117 sourceBody357_0

def sourceBody357_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_88 sourceBody357_118

def sourceBody357_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_87 sourceBody357_119

def sourceBody357_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_83 sourceBody357_120

def sourceBody357_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_82 sourceBody357_121

def sourceBody357_123 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
  PUnit.unit Flapjack.Spt.ln) sourceBody357_122 (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
    PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody357_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_123 sourceBody357_5

def sourceBody357_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_5 sourceBody357_124

def sourceBody357_126 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 42, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody357_127 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 14)

def sourceBody357_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_127 sourceBody357_0

def sourceBody357_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_128 sourceBody357_0

def sourceBody357_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_126 sourceBody357_129

def sourceBody357_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_0 sourceBody357_130

def sourceBody357_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_125 sourceBody357_131

def sourceBody357_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_81 sourceBody357_132

def sourceBody357_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_0 sourceBody357_133

def sourceBody357_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_80 sourceBody357_134

def sourceBody357_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_0 sourceBody357_135

def sourceBody357_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_79 sourceBody357_136

def sourceBody357_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_47 sourceBody357_137

def sourceBody357_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_0 sourceBody357_138

def sourceBody357_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_0 sourceBody357_139

def sourceBody357_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_41 sourceBody357_140

def sourceBody357_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_40 sourceBody357_141

def sourceBody357_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_34 sourceBody357_142

def sourceBody357_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_0 sourceBody357_143

def sourceBody357_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_33 sourceBody357_144

def sourceBody357_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_32 sourceBody357_145

def sourceBody357_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_146 sourceBody357_113

def sourceBody357_148 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 40 (Flapjack.WordRegImm.imm 0#64) sourceBody357_147 sourceBody357_115

def sourceBody357_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_148 sourceBody357_5

def sourceBody357_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_149 sourceBody357_0

def sourceBody357_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_26 sourceBody357_150

def sourceBody357_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_25 sourceBody357_151

def sourceBody357_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_21 sourceBody357_152

def sourceBody357_154 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_20 sourceBody357_153

def sourceBody357_155 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
    PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
  PUnit.unit Flapjack.Spt.ln) sourceBody357_154 (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln)
  PUnit.unit Flapjack.Spt.ln)

def sourceBody357_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_155 sourceBody357_5

def sourceBody357_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_5 sourceBody357_156

def sourceBody357_158 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 22, Flapjack.WordLangExpHOL.var 2])

def sourceBody357_159 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [10]

def sourceBody357_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_159 sourceBody357_0

def sourceBody357_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_158 sourceBody357_160

def sourceBody357_162 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_157 sourceBody357_161

def sourceBody357_163 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_19 sourceBody357_162

def sourceBody357_164 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_0 sourceBody357_163

def sourceBody357_165 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_18 sourceBody357_164

def sourceBody357_166 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_0 sourceBody357_165

def sourceBody357_167 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_17 sourceBody357_166

def sourceBody357_168 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_0 sourceBody357_167

def sourceBody357_169 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_0 sourceBody357_168

def sourceBody357_170 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_9 sourceBody357_169

def sourceBody357_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_0 sourceBody357_170

def sourceBody357_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody357_0 sourceBody357_171

def source357 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (357, 4, sourceBody357_172)
end InitECandidate.Proofs.WordStages
