import InitECandidate.Proofs.WordStages.Source429
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody445_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody445_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 248#64]))

def sourceBody445_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 10)

def sourceBody445_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 224#64]))

def sourceBody445_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody445_5 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody445_0, 445, 2)) (some 87) ([6, 18]) (some (6, sourceBody445_4, 445, 3))

def sourceBody445_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody445_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_5 sourceBody445_6

def sourceBody445_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_7 sourceBody445_0

def sourceBody445_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_3 sourceBody445_8

def sourceBody445_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_2 sourceBody445_9

def sourceBody445_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_0 sourceBody445_10

def sourceBody445_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_0 sourceBody445_11

def sourceBody445_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 8#64])

def sourceBody445_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 2)

def sourceBody445_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 20#64)

def sourceBody445_16 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody445_0, 445, 4)) (some 77) ([6, 18, 14]) (some (6, sourceBody445_4, 445, 5))

def sourceBody445_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_16 sourceBody445_6

def sourceBody445_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_17 sourceBody445_0

def sourceBody445_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_15 sourceBody445_18

def sourceBody445_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_14 sourceBody445_19

def sourceBody445_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_13 sourceBody445_20

def sourceBody445_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_0 sourceBody445_21

def sourceBody445_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_0 sourceBody445_22

def sourceBody445_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_12 sourceBody445_23

def sourceBody445_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 232#64]))

def sourceBody445_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 10)

def sourceBody445_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody445_28 : WordLangProgHOL (BitVec 64) :=
.call (some (([20, 6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody445_0, 445, 6)) (some 186) ([18, 14]) (some (18, sourceBody445_27, 445, 7))

def sourceBody445_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_28 sourceBody445_6

def sourceBody445_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_29 sourceBody445_0

def sourceBody445_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_26 sourceBody445_30

def sourceBody445_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_25 sourceBody445_31

def sourceBody445_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 20)

def sourceBody445_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody445_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody445_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody445_37 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.WordRegImm.reg 24) sourceBody445_35 sourceBody445_36

def sourceBody445_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_37 sourceBody445_6

def sourceBody445_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 14)

def sourceBody445_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 6)

def sourceBody445_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [18]

def sourceBody445_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_41 sourceBody445_0

def sourceBody445_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_40 sourceBody445_42

def sourceBody445_44 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 4 (Flapjack.WordRegImm.imm 0#64) sourceBody445_43 sourceBody445_0

def sourceBody445_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_44 sourceBody445_6

def sourceBody445_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_45 sourceBody445_0

def sourceBody445_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_39 sourceBody445_46

def sourceBody445_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_38 sourceBody445_47

def sourceBody445_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_34 sourceBody445_48

def sourceBody445_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_33 sourceBody445_49

def sourceBody445_51 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 2)

def sourceBody445_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody445_53 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody445_0, 445, 8)) (some 443) ([14]) (some (14, sourceBody445_52, 445, 9))

def sourceBody445_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_53 sourceBody445_6

def sourceBody445_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_54 sourceBody445_0

def sourceBody445_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_51 sourceBody445_55

def sourceBody445_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 80#64)

def sourceBody445_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 24

def sourceBody445_59 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody445_0, 445, 10)) (some 68) ([24]) (some (24, sourceBody445_58, 445, 11))

def sourceBody445_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_59 sourceBody445_6

def sourceBody445_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_60 sourceBody445_0

def sourceBody445_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_57 sourceBody445_61

def sourceBody445_63 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 80#64)

def sourceBody445_64 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 4

def sourceBody445_65 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody445_0, 445, 12)) (some 78) ([4, 16]) (some (4, sourceBody445_64, 445, 13))

def sourceBody445_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_65 sourceBody445_6

def sourceBody445_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_66 sourceBody445_0

def sourceBody445_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_63 sourceBody445_67

def sourceBody445_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_39 sourceBody445_68

def sourceBody445_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_0 sourceBody445_69

def sourceBody445_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_0 sourceBody445_70

def sourceBody445_72 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 48#64])

def sourceBody445_73 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 136#64]))

def sourceBody445_74 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody445_75 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody445_0, 445, 14)) (some 77) ([4, 16, 12]) (some (4, sourceBody445_64, 445, 15))

def sourceBody445_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_75 sourceBody445_6

def sourceBody445_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_76 sourceBody445_0

def sourceBody445_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_74 sourceBody445_77

def sourceBody445_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_73 sourceBody445_78

def sourceBody445_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_72 sourceBody445_79

def sourceBody445_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_0 sourceBody445_80

def sourceBody445_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_0 sourceBody445_81

def sourceBody445_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_71 sourceBody445_82

def sourceBody445_84 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 18)

def sourceBody445_85 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody445_86 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody445_87 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody445_88 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 4 (Flapjack.WordRegImm.reg 16) sourceBody445_86 sourceBody445_87

def sourceBody445_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_88 sourceBody445_6

def sourceBody445_90 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 4)

def sourceBody445_91 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 14)

def sourceBody445_92 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 4)

def sourceBody445_93 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 24) 16

def sourceBody445_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_93 sourceBody445_0

def sourceBody445_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_92 sourceBody445_94

def sourceBody445_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_95 sourceBody445_0

def sourceBody445_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_86 sourceBody445_96

def sourceBody445_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_0 sourceBody445_97

def sourceBody445_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_91 sourceBody445_98

def sourceBody445_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_0 sourceBody445_99

def sourceBody445_101 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 8#64])

def sourceBody445_102 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 0#64]))

def sourceBody445_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_102 sourceBody445_96

def sourceBody445_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_0 sourceBody445_103

def sourceBody445_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_101 sourceBody445_104

def sourceBody445_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_0 sourceBody445_105

def sourceBody445_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_100 sourceBody445_106

def sourceBody445_108 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 16#64])

def sourceBody445_109 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody445_110 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 8#64],
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody445_111 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 8#64],
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody445_112 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 8#64],
        Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody445_113 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 4)

def sourceBody445_114 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 24) 8

def sourceBody445_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_114 sourceBody445_0

def sourceBody445_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_113 sourceBody445_115

def sourceBody445_117 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 16)

def sourceBody445_118 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 24, Flapjack.WordLangExpHOL.const 8#64]) 8

def sourceBody445_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_118 sourceBody445_0

def sourceBody445_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_117 sourceBody445_119

def sourceBody445_121 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 12)

def sourceBody445_122 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 24, Flapjack.WordLangExpHOL.const 16#64])
  8

def sourceBody445_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_122 sourceBody445_0

def sourceBody445_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_121 sourceBody445_123

def sourceBody445_125 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 22)

def sourceBody445_126 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 24, Flapjack.WordLangExpHOL.const 24#64])
  8

def sourceBody445_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_126 sourceBody445_0

def sourceBody445_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_125 sourceBody445_127

def sourceBody445_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_128 sourceBody445_0

def sourceBody445_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_124 sourceBody445_129

def sourceBody445_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_120 sourceBody445_130

def sourceBody445_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_116 sourceBody445_131

def sourceBody445_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_112 sourceBody445_132

def sourceBody445_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_0 sourceBody445_133

def sourceBody445_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_111 sourceBody445_134

def sourceBody445_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_0 sourceBody445_135

def sourceBody445_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_110 sourceBody445_136

def sourceBody445_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_0 sourceBody445_137

def sourceBody445_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_109 sourceBody445_138

def sourceBody445_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_0 sourceBody445_139

def sourceBody445_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_108 sourceBody445_140

def sourceBody445_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_0 sourceBody445_141

def sourceBody445_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_107 sourceBody445_142

def sourceBody445_144 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 48#64]))

def sourceBody445_145 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody445_0, 445, 16)) (some 77) ([4, 16, 12]) (some (4, sourceBody445_64, 445, 17))

def sourceBody445_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_145 sourceBody445_6

def sourceBody445_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_146 sourceBody445_0

def sourceBody445_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_74 sourceBody445_147

def sourceBody445_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_144 sourceBody445_148

def sourceBody445_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_72 sourceBody445_149

def sourceBody445_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_0 sourceBody445_150

def sourceBody445_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_0 sourceBody445_151

def sourceBody445_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_143 sourceBody445_152

def sourceBody445_154 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.imm 0#64) sourceBody445_153 sourceBody445_0

def sourceBody445_155 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_154 sourceBody445_6

def sourceBody445_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_155 sourceBody445_0

def sourceBody445_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_90 sourceBody445_156

def sourceBody445_158 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_89 sourceBody445_157

def sourceBody445_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_85 sourceBody445_158

def sourceBody445_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_84 sourceBody445_159

def sourceBody445_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_83 sourceBody445_160

def sourceBody445_162 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 10)

def sourceBody445_163 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 224#64]))

def sourceBody445_164 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody445_0, 445, 18)) (some 87) ([4, 16]) (some (4, sourceBody445_64, 445, 19))

def sourceBody445_165 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_164 sourceBody445_6

def sourceBody445_166 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_165 sourceBody445_0

def sourceBody445_167 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_163 sourceBody445_166

def sourceBody445_168 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_162 sourceBody445_167

def sourceBody445_169 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_0 sourceBody445_168

def sourceBody445_170 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_0 sourceBody445_169

def sourceBody445_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_161 sourceBody445_170

def sourceBody445_172 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 8#64])

def sourceBody445_173 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 2)

def sourceBody445_174 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 20#64)

def sourceBody445_175 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody445_0, 445, 20)) (some 77) ([4, 16, 12]) (some (4, sourceBody445_64, 445, 21))

def sourceBody445_176 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_175 sourceBody445_6

def sourceBody445_177 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_176 sourceBody445_0

def sourceBody445_178 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_174 sourceBody445_177

def sourceBody445_179 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_173 sourceBody445_178

def sourceBody445_180 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_172 sourceBody445_179

def sourceBody445_181 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_0 sourceBody445_180

def sourceBody445_182 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_0 sourceBody445_181

def sourceBody445_183 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_171 sourceBody445_182

def sourceBody445_184 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 232#64]))

def sourceBody445_185 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 10)

def sourceBody445_186 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 14)

def sourceBody445_187 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody445_0, 445, 22)) (some 192) ([4, 16, 12]) (some (4, sourceBody445_64, 445, 23))

def sourceBody445_188 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_187 sourceBody445_6

def sourceBody445_189 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_188 sourceBody445_0

def sourceBody445_190 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_186 sourceBody445_189

def sourceBody445_191 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_185 sourceBody445_190

def sourceBody445_192 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_184 sourceBody445_191

def sourceBody445_193 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_0 sourceBody445_192

def sourceBody445_194 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_0 sourceBody445_193

def sourceBody445_195 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_183 sourceBody445_194

def sourceBody445_196 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [24]

def sourceBody445_197 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_196 sourceBody445_0

def sourceBody445_198 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_91 sourceBody445_197

def sourceBody445_199 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_195 sourceBody445_198

def sourceBody445_200 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_62 sourceBody445_199

def sourceBody445_201 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_0 sourceBody445_200

def sourceBody445_202 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_0 sourceBody445_201

def sourceBody445_203 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_56 sourceBody445_202

def sourceBody445_204 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_0 sourceBody445_203

def sourceBody445_205 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_0 sourceBody445_204

def sourceBody445_206 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_50 sourceBody445_205

def sourceBody445_207 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_32 sourceBody445_206

def sourceBody445_208 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_0 sourceBody445_207

def sourceBody445_209 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_0 sourceBody445_208

def sourceBody445_210 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_0 sourceBody445_209

def sourceBody445_211 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_0 sourceBody445_210

def sourceBody445_212 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_24 sourceBody445_211

def sourceBody445_213 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_1 sourceBody445_212

def sourceBody445_214 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody445_0 sourceBody445_213

def source445 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (445, 2, sourceBody445_214)
end InitECandidate.Proofs.WordStages
