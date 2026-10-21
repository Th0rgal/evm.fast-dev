import InitECandidate.Proofs.WordStages.Source782
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody798_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody798_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 36

def sourceBody798_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody798_0, 798, 2)) (some 69) ([]) (some (36, sourceBody798_1, 798, 3))

def sourceBody798_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody798_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_2 sourceBody798_3

def sourceBody798_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_4 sourceBody798_0

def sourceBody798_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 96#64)

def sourceBody798_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody798_8 : WordLangProgHOL (BitVec 64) :=
.call (some (([36]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit))
      PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody798_0, 798, 4)) (some 68) ([14]) (some (14, sourceBody798_7, 798, 5))

def sourceBody798_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_8 sourceBody798_3

def sourceBody798_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_9 sourceBody798_0

def sourceBody798_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_6 sourceBody798_10

def sourceBody798_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 96#64)

def sourceBody798_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 28

def sourceBody798_14 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody798_0, 798, 6)) (some 68) ([28]) (some (28, sourceBody798_13, 798, 7))

def sourceBody798_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_14 sourceBody798_3

def sourceBody798_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_15 sourceBody798_0

def sourceBody798_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_12 sourceBody798_16

def sourceBody798_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody798_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 96#64)

def sourceBody798_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.longMul 16 16 20 34))

def sourceBody798_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 36)

def sourceBody798_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.var 16])

def sourceBody798_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody798_24 : WordLangProgHOL (BitVec 64) :=
.call (some (([28]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody798_0, 798, 8)) (some 725) ([30, 24]) (some (20, sourceBody798_23, 798, 9))

def sourceBody798_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_24 sourceBody798_3

def sourceBody798_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_25 sourceBody798_0

def sourceBody798_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_22 sourceBody798_26

def sourceBody798_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_21 sourceBody798_27

def sourceBody798_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_20 sourceBody798_28

def sourceBody798_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_19 sourceBody798_29

def sourceBody798_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_18 sourceBody798_30

def sourceBody798_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_0 sourceBody798_31

def sourceBody798_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_0 sourceBody798_32

def sourceBody798_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody798_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 28)

def sourceBody798_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody798_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody798_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody798_39 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 34 (Flapjack.WordRegImm.reg 16) sourceBody798_37 sourceBody798_38

def sourceBody798_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_39 sourceBody798_3

def sourceBody798_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 34)

def sourceBody798_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 36)

def sourceBody798_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 36)

def sourceBody798_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 8)

def sourceBody798_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 34

def sourceBody798_46 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody798_0, 798, 10)) (some 735) ([34, 16, 30]) (some (34, sourceBody798_45, 798, 11))

def sourceBody798_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_46 sourceBody798_3

def sourceBody798_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_47 sourceBody798_0

def sourceBody798_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_44 sourceBody798_48

def sourceBody798_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_43 sourceBody798_49

def sourceBody798_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_42 sourceBody798_50

def sourceBody798_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_0 sourceBody798_51

def sourceBody798_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_0 sourceBody798_52

def sourceBody798_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 96#64)

def sourceBody798_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.longMul 30 30 34 16))

def sourceBody798_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 2#64],
      Flapjack.WordLangExpHOL.var 28])

def sourceBody798_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.const 96#64)

def sourceBody798_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.longMul 12 12 24 38))

def sourceBody798_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 14)

def sourceBody798_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.var 30])

def sourceBody798_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.var 12])

def sourceBody798_62 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody798_0, 798, 12)) (some 735) ([26, 18, 32]) (some (34, sourceBody798_45, 798, 13))

def sourceBody798_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_62 sourceBody798_3

def sourceBody798_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_63 sourceBody798_0

def sourceBody798_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_61 sourceBody798_64

def sourceBody798_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_60 sourceBody798_65

def sourceBody798_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_59 sourceBody798_66

def sourceBody798_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_58 sourceBody798_67

def sourceBody798_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_57 sourceBody798_68

def sourceBody798_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_56 sourceBody798_69

def sourceBody798_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_55 sourceBody798_70

def sourceBody798_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_54 sourceBody798_71

def sourceBody798_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_35 sourceBody798_72

def sourceBody798_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_0 sourceBody798_73

def sourceBody798_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_0 sourceBody798_74

def sourceBody798_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_53 sourceBody798_75

def sourceBody798_77 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 14)

def sourceBody798_78 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody798_0, 798, 14)) (some 730) ([34, 16, 30]) (some (34, sourceBody798_45, 798, 15))

def sourceBody798_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_78 sourceBody798_3

def sourceBody798_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_79 sourceBody798_0

def sourceBody798_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_77 sourceBody798_80

def sourceBody798_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_43 sourceBody798_81

def sourceBody798_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_42 sourceBody798_82

def sourceBody798_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_0 sourceBody798_83

def sourceBody798_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_0 sourceBody798_84

def sourceBody798_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_76 sourceBody798_85

def sourceBody798_87 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 28, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody798_88 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 20)

def sourceBody798_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_88 sourceBody798_0

def sourceBody798_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_89 sourceBody798_0

def sourceBody798_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_87 sourceBody798_90

def sourceBody798_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_0 sourceBody798_91

def sourceBody798_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_86 sourceBody798_92

def sourceBody798_94 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody798_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_93 sourceBody798_94

def sourceBody798_96 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody798_97 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 30 (Flapjack.WordRegImm.imm 0#64) sourceBody798_95 sourceBody798_96

def sourceBody798_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_97 sourceBody798_3

def sourceBody798_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_98 sourceBody798_0

def sourceBody798_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_41 sourceBody798_99

def sourceBody798_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_40 sourceBody798_100

def sourceBody798_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_36 sourceBody798_101

def sourceBody798_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_35 sourceBody798_102

def sourceBody798_104 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit Flapjack.Spt.ln) sourceBody798_103 (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
    PUnit.unit
    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      Flapjack.Spt.ln))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody798_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_104 sourceBody798_3

def sourceBody798_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_3 sourceBody798_105

def sourceBody798_107 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 2)

def sourceBody798_108 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody798_0, 798, 16)) (some 725) ([34, 16]) (some (34, sourceBody798_45, 798, 17))

def sourceBody798_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_108 sourceBody798_3

def sourceBody798_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_109 sourceBody798_0

def sourceBody798_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_43 sourceBody798_110

def sourceBody798_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_107 sourceBody798_111

def sourceBody798_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_0 sourceBody798_112

def sourceBody798_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_0 sourceBody798_113

def sourceBody798_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_106 sourceBody798_114

def sourceBody798_116 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 22)

def sourceBody798_117 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody798_0, 798, 18)) (some 70) ([34]) (some (34, sourceBody798_45, 798, 19))

def sourceBody798_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_117 sourceBody798_3

def sourceBody798_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_118 sourceBody798_0

def sourceBody798_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_116 sourceBody798_119

def sourceBody798_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_0 sourceBody798_120

def sourceBody798_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_0 sourceBody798_121

def sourceBody798_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_115 sourceBody798_122

def sourceBody798_124 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody798_125 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [20]

def sourceBody798_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_125 sourceBody798_0

def sourceBody798_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_124 sourceBody798_126

def sourceBody798_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_123 sourceBody798_127

def sourceBody798_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_34 sourceBody798_128

def sourceBody798_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_0 sourceBody798_129

def sourceBody798_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_33 sourceBody798_130

def sourceBody798_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_17 sourceBody798_131

def sourceBody798_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_0 sourceBody798_132

def sourceBody798_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_0 sourceBody798_133

def sourceBody798_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_11 sourceBody798_134

def sourceBody798_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_0 sourceBody798_135

def sourceBody798_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_0 sourceBody798_136

def sourceBody798_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_5 sourceBody798_137

def sourceBody798_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_0 sourceBody798_138

def sourceBody798_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody798_0 sourceBody798_139

def source798 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (798, 6, sourceBody798_140)
end InitECandidate.Proofs.WordStages
