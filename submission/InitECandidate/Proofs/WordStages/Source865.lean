import InitECandidate.Proofs.WordStages.Source849
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody865_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody865_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 0#64]))

def sourceBody865_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 72#64]))

def sourceBody865_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 80#64]))

def sourceBody865_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 28

def sourceBody865_5 : WordLangProgHOL (BitVec 64) :=
.call (some (([34, 8]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody865_0, 865, 2)) (some 274) ([28, 20]) (some (28, sourceBody865_4, 865, 3))

def sourceBody865_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody865_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_5 sourceBody865_6

def sourceBody865_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_7 sourceBody865_0

def sourceBody865_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_3 sourceBody865_8

def sourceBody865_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_2 sourceBody865_9

def sourceBody865_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 80#64]))

def sourceBody865_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 28)

def sourceBody865_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody865_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody865_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody865_16 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 40 (Flapjack.WordRegImm.reg 6) sourceBody865_14 sourceBody865_15

def sourceBody865_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_16 sourceBody865_6

def sourceBody865_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 40)

def sourceBody865_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 3#64)

def sourceBody865_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 20)

def sourceBody865_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_20 sourceBody865_0

def sourceBody865_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_21 sourceBody865_0

def sourceBody865_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_19 sourceBody865_22

def sourceBody865_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_0 sourceBody865_23

def sourceBody865_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 4#64)

def sourceBody865_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody865_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_25 sourceBody865_26

def sourceBody865_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_24 sourceBody865_27

def sourceBody865_29 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 26 (Flapjack.WordRegImm.imm 0#64) sourceBody865_28 sourceBody865_0

def sourceBody865_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_29 sourceBody865_6

def sourceBody865_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_30 sourceBody865_0

def sourceBody865_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_18 sourceBody865_31

def sourceBody865_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_17 sourceBody865_32

def sourceBody865_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_13 sourceBody865_33

def sourceBody865_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_12 sourceBody865_34

def sourceBody865_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 34,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
            [Flapjack.WordLangExpHOL.var 28, Flapjack.WordLangExpHOL.const 1#64])
          (Flapjack.WordLangExpHOL.const 3#64)]))

def sourceBody865_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
        [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
          Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
            (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
      Flapjack.WordLangExpHOL.const 440#64])

def sourceBody865_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 8)

def sourceBody865_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 6)

def sourceBody865_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 40) 26

def sourceBody865_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_40 sourceBody865_0

def sourceBody865_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_39 sourceBody865_41

def sourceBody865_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_42 sourceBody865_0

def sourceBody865_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_38 sourceBody865_43

def sourceBody865_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_0 sourceBody865_44

def sourceBody865_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_37 sourceBody865_45

def sourceBody865_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_0 sourceBody865_46

def sourceBody865_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
        [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
          Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
            (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
      Flapjack.WordLangExpHOL.const 448#64])

def sourceBody865_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 28)

def sourceBody865_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_49 sourceBody865_43

def sourceBody865_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_0 sourceBody865_50

def sourceBody865_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_48 sourceBody865_51

def sourceBody865_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_0 sourceBody865_52

def sourceBody865_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_47 sourceBody865_53

def sourceBody865_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 40#64]))

def sourceBody865_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 48#64]))

def sourceBody865_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody865_58 : WordLangProgHOL (BitVec 64) :=
.call (some (([40]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody865_0, 865, 4)) (some 289) ([6, 26]) (some (6, sourceBody865_57, 865, 5))

def sourceBody865_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_58 sourceBody865_6

def sourceBody865_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_59 sourceBody865_0

def sourceBody865_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_56 sourceBody865_60

def sourceBody865_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_55 sourceBody865_61

def sourceBody865_63 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 56#64]))

def sourceBody865_64 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 64#64]))

def sourceBody865_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 26

def sourceBody865_66 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody865_0, 865, 6)) (some 289) ([26, 18]) (some (26, sourceBody865_65, 865, 7))

def sourceBody865_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_66 sourceBody865_6

def sourceBody865_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_67 sourceBody865_0

def sourceBody865_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_64 sourceBody865_68

def sourceBody865_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_63 sourceBody865_69

def sourceBody865_71 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 40)

def sourceBody865_72 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 20, Flapjack.WordLangExpHOL.const 32#64]))

def sourceBody865_73 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 6)

def sourceBody865_74 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody865_75 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody865_0, 865, 8)) (some 382) ([18, 38, 12]) (some (18, sourceBody865_74, 865, 9))

def sourceBody865_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_75 sourceBody865_6

def sourceBody865_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_76 sourceBody865_0

def sourceBody865_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_73 sourceBody865_77

def sourceBody865_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_72 sourceBody865_78

def sourceBody865_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_71 sourceBody865_79

def sourceBody865_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_0 sourceBody865_80

def sourceBody865_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_0 sourceBody865_81

def sourceBody865_83 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 32#64]))

def sourceBody865_84 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 40#64]))

def sourceBody865_85 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody865_86 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 38)

def sourceBody865_87 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 18)

def sourceBody865_88 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody865_89 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody865_90 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.less) 32 (Flapjack.WordRegImm.reg 22) sourceBody865_88 sourceBody865_89

def sourceBody865_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_90 sourceBody865_6

def sourceBody865_92 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 32)

def sourceBody865_93 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 26,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 38)
          (Flapjack.WordLangExpHOL.const 4#64),
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody865_94 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody865_95 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 32 (Flapjack.WordRegImm.reg 22) sourceBody865_88 sourceBody865_89

def sourceBody865_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_95 sourceBody865_6

def sourceBody865_97 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 4#64)

def sourceBody865_98 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 12)

def sourceBody865_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_98 sourceBody865_0

def sourceBody865_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_99 sourceBody865_0

def sourceBody865_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_97 sourceBody865_100

def sourceBody865_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_0 sourceBody865_101

def sourceBody865_103 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody865_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_97 sourceBody865_103

def sourceBody865_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_102 sourceBody865_104

def sourceBody865_106 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 42 (Flapjack.WordRegImm.imm 0#64) sourceBody865_105 sourceBody865_0

def sourceBody865_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_106 sourceBody865_6

def sourceBody865_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_107 sourceBody865_0

def sourceBody865_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_92 sourceBody865_108

def sourceBody865_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_96 sourceBody865_109

def sourceBody865_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_94 sourceBody865_110

def sourceBody865_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_93 sourceBody865_111

def sourceBody865_113 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 38, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody865_114 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 12)

def sourceBody865_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_114 sourceBody865_0

def sourceBody865_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_115 sourceBody865_0

def sourceBody865_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_113 sourceBody865_116

def sourceBody865_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_0 sourceBody865_117

def sourceBody865_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_112 sourceBody865_118

def sourceBody865_120 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody865_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_119 sourceBody865_120

def sourceBody865_122 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody865_123 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 42 (Flapjack.WordRegImm.imm 0#64) sourceBody865_121 sourceBody865_122

def sourceBody865_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_123 sourceBody865_6

def sourceBody865_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_124 sourceBody865_0

def sourceBody865_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_92 sourceBody865_125

def sourceBody865_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_91 sourceBody865_126

def sourceBody865_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_87 sourceBody865_127

def sourceBody865_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_86 sourceBody865_128

def sourceBody865_130 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit
    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)))
  PUnit.unit Flapjack.Spt.ln) sourceBody865_129 (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody865_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_130 sourceBody865_6

def sourceBody865_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_6 sourceBody865_131

def sourceBody865_133 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 2)

def sourceBody865_134 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 32

def sourceBody865_135 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody865_0, 865, 10)) (some 850) ([32]) (some (32, sourceBody865_134, 865, 11))

def sourceBody865_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_135 sourceBody865_6

def sourceBody865_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_136 sourceBody865_0

def sourceBody865_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_133 sourceBody865_137

def sourceBody865_139 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody865_140 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 22

def sourceBody865_141 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody865_0, 865, 12)) (some 68) ([22]) (some (22, sourceBody865_140, 865, 13))

def sourceBody865_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_141 sourceBody865_6

def sourceBody865_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_142 sourceBody865_0

def sourceBody865_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_139 sourceBody865_143

def sourceBody865_145 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 12)

def sourceBody865_146 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 32)

def sourceBody865_147 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 42

def sourceBody865_148 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody865_0, 865, 14)) (some 273) ([42, 4]) (some (42, sourceBody865_147, 865, 15))

def sourceBody865_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_148 sourceBody865_6

def sourceBody865_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_149 sourceBody865_0

def sourceBody865_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_146 sourceBody865_150

def sourceBody865_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_145 sourceBody865_151

def sourceBody865_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_0 sourceBody865_152

def sourceBody865_154 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_0 sourceBody865_153

def sourceBody865_155 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 0#64]),
      Flapjack.WordLangExpHOL.const 472#64])

def sourceBody865_156 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody865_157 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody865_0, 865, 16)) (some 79) ([42, 4, 24]) (some (42, sourceBody865_147, 865, 17))

def sourceBody865_158 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_157 sourceBody865_6

def sourceBody865_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_158 sourceBody865_0

def sourceBody865_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_156 sourceBody865_159

def sourceBody865_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_155 sourceBody865_160

def sourceBody865_162 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_92 sourceBody865_161

def sourceBody865_163 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 22)

def sourceBody865_164 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody865_165 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody865_166 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody865_167 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 4 (Flapjack.WordRegImm.reg 24) sourceBody865_165 sourceBody865_166

def sourceBody865_168 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_167 sourceBody865_6

def sourceBody865_169 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 4)

def sourceBody865_170 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.const 5#64)

def sourceBody865_171 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 42)

def sourceBody865_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_171 sourceBody865_0

def sourceBody865_173 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_172 sourceBody865_0

def sourceBody865_174 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_170 sourceBody865_173

def sourceBody865_175 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_0 sourceBody865_174

def sourceBody865_176 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.const 4#64)

def sourceBody865_177 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_176 sourceBody865_147

def sourceBody865_178 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_175 sourceBody865_177

def sourceBody865_179 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 16 (Flapjack.WordRegImm.imm 0#64) sourceBody865_178 sourceBody865_0

def sourceBody865_180 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_179 sourceBody865_6

def sourceBody865_181 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_180 sourceBody865_0

def sourceBody865_182 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_169 sourceBody865_181

def sourceBody865_183 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_168 sourceBody865_182

def sourceBody865_184 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_164 sourceBody865_183

def sourceBody865_185 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_163 sourceBody865_184

def sourceBody865_186 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 2)

def sourceBody865_187 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 4

def sourceBody865_188 : WordLangProgHOL (BitVec 64) :=
.call (some (([42]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody865_0, 865, 18)) (some 854) ([4]) (some (4, sourceBody865_187, 865, 19))

def sourceBody865_189 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_188 sourceBody865_6

def sourceBody865_190 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_189 sourceBody865_0

def sourceBody865_191 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_186 sourceBody865_190

def sourceBody865_192 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 42)

def sourceBody865_193 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody865_194 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody865_195 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 24 (Flapjack.WordRegImm.reg 16) sourceBody865_194 sourceBody865_164

def sourceBody865_196 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_195 sourceBody865_6

def sourceBody865_197 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 24)

def sourceBody865_198 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 6#64)

def sourceBody865_199 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 4)

def sourceBody865_200 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_199 sourceBody865_0

def sourceBody865_201 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_200 sourceBody865_0

def sourceBody865_202 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_198 sourceBody865_201

def sourceBody865_203 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_0 sourceBody865_202

def sourceBody865_204 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 4#64)

def sourceBody865_205 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_204 sourceBody865_187

def sourceBody865_206 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_203 sourceBody865_205

def sourceBody865_207 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 36 (Flapjack.WordRegImm.imm 0#64) sourceBody865_206 sourceBody865_0

def sourceBody865_208 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_207 sourceBody865_6

def sourceBody865_209 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_208 sourceBody865_0

def sourceBody865_210 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_197 sourceBody865_209

def sourceBody865_211 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_196 sourceBody865_210

def sourceBody865_212 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_193 sourceBody865_211

def sourceBody865_213 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_192 sourceBody865_212

def sourceBody865_214 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 20)

def sourceBody865_215 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 12)

def sourceBody865_216 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 24

def sourceBody865_217 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody865_0, 865, 20)) (some 281) ([24, 16]) (some (24, sourceBody865_216, 865, 21))

def sourceBody865_218 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_217 sourceBody865_6

def sourceBody865_219 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_218 sourceBody865_0

def sourceBody865_220 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_215 sourceBody865_219

def sourceBody865_221 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_214 sourceBody865_220

def sourceBody865_222 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_0 sourceBody865_221

def sourceBody865_223 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_0 sourceBody865_222

def sourceBody865_224 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_213 sourceBody865_223

def sourceBody865_225 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 120#64)

def sourceBody865_226 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody865_0, 865, 22)) (some 68) ([24]) (some (24, sourceBody865_216, 865, 23))

def sourceBody865_227 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_226 sourceBody865_6

def sourceBody865_228 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_227 sourceBody865_0

def sourceBody865_229 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_225 sourceBody865_228

def sourceBody865_230 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
        [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
          Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
            (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
      Flapjack.WordLangExpHOL.const 408#64])

def sourceBody865_231 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 16)

def sourceBody865_232 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 24) 36

def sourceBody865_233 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_232 sourceBody865_0

def sourceBody865_234 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_231 sourceBody865_233

def sourceBody865_235 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_234 sourceBody865_0

def sourceBody865_236 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_169 sourceBody865_235

def sourceBody865_237 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_0 sourceBody865_236

def sourceBody865_238 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_230 sourceBody865_237

def sourceBody865_239 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_0 sourceBody865_238

def sourceBody865_240 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_229 sourceBody865_239

def sourceBody865_241 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_0 sourceBody865_240

def sourceBody865_242 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_0 sourceBody865_241

def sourceBody865_243 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_224 sourceBody865_242

def sourceBody865_244 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 408#64]))

def sourceBody865_245 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 120#64)

def sourceBody865_246 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody865_0, 865, 24)) (some 78) ([24, 16]) (some (24, sourceBody865_216, 865, 25))

def sourceBody865_247 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_246 sourceBody865_6

def sourceBody865_248 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_247 sourceBody865_0

def sourceBody865_249 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_245 sourceBody865_248

def sourceBody865_250 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_244 sourceBody865_249

def sourceBody865_251 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_0 sourceBody865_250

def sourceBody865_252 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_0 sourceBody865_251

def sourceBody865_253 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_243 sourceBody865_252

def sourceBody865_254 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 408#64]),
      Flapjack.WordLangExpHOL.const 0#64])

def sourceBody865_255 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 88#64]))

def sourceBody865_256 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 24)

def sourceBody865_257 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 4) 16

def sourceBody865_258 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_257 sourceBody865_0

def sourceBody865_259 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_256 sourceBody865_258

def sourceBody865_260 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_259 sourceBody865_0

def sourceBody865_261 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_255 sourceBody865_260

def sourceBody865_262 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_0 sourceBody865_261

def sourceBody865_263 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_254 sourceBody865_262

def sourceBody865_264 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_0 sourceBody865_263

def sourceBody865_265 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_253 sourceBody865_264

def sourceBody865_266 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 408#64]),
      Flapjack.WordLangExpHOL.const 8#64])

def sourceBody865_267 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 104#64]))

def sourceBody865_268 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_267 sourceBody865_260

def sourceBody865_269 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_0 sourceBody865_268

def sourceBody865_270 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_266 sourceBody865_269

def sourceBody865_271 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_0 sourceBody865_270

def sourceBody865_272 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_265 sourceBody865_271

def sourceBody865_273 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 408#64]),
      Flapjack.WordLangExpHOL.const 16#64])

def sourceBody865_274 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 440#64]))

def sourceBody865_275 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_274 sourceBody865_260

def sourceBody865_276 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_0 sourceBody865_275

def sourceBody865_277 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_273 sourceBody865_276

def sourceBody865_278 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_0 sourceBody865_277

def sourceBody865_279 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_272 sourceBody865_278

def sourceBody865_280 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 408#64]),
      Flapjack.WordLangExpHOL.const 24#64])

def sourceBody865_281 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 448#64]))

def sourceBody865_282 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_281 sourceBody865_260

def sourceBody865_283 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_0 sourceBody865_282

def sourceBody865_284 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_280 sourceBody865_283

def sourceBody865_285 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_0 sourceBody865_284

def sourceBody865_286 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_279 sourceBody865_285

def sourceBody865_287 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 408#64]),
      Flapjack.WordLangExpHOL.const 32#64])

def sourceBody865_288 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody865_289 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_288 sourceBody865_260

def sourceBody865_290 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_0 sourceBody865_289

def sourceBody865_291 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_287 sourceBody865_290

def sourceBody865_292 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_0 sourceBody865_291

def sourceBody865_293 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_286 sourceBody865_292

def sourceBody865_294 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 408#64]),
      Flapjack.WordLangExpHOL.const 40#64])

def sourceBody865_295 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 96#64]))

def sourceBody865_296 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_295 sourceBody865_260

def sourceBody865_297 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_0 sourceBody865_296

def sourceBody865_298 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_294 sourceBody865_297

def sourceBody865_299 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_0 sourceBody865_298

def sourceBody865_300 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_293 sourceBody865_299

def sourceBody865_301 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 408#64]),
      Flapjack.WordLangExpHOL.const 48#64])

def sourceBody865_302 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 160#64]))

def sourceBody865_303 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 160#64],
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody865_304 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 160#64],
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody865_305 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 160#64],
        Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody865_306 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 24)

def sourceBody865_307 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 4) 30

def sourceBody865_308 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_307 sourceBody865_0

def sourceBody865_309 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_306 sourceBody865_308

def sourceBody865_310 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 16)

def sourceBody865_311 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 8#64]) 30

def sourceBody865_312 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_311 sourceBody865_0

def sourceBody865_313 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_310 sourceBody865_312

def sourceBody865_314 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 36)

def sourceBody865_315 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 16#64])
  30

def sourceBody865_316 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_315 sourceBody865_0

def sourceBody865_317 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_314 sourceBody865_316

def sourceBody865_318 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 10)

def sourceBody865_319 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 24#64])
  30

def sourceBody865_320 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_319 sourceBody865_0

def sourceBody865_321 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_318 sourceBody865_320

def sourceBody865_322 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_321 sourceBody865_0

def sourceBody865_323 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_317 sourceBody865_322

def sourceBody865_324 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_313 sourceBody865_323

def sourceBody865_325 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_309 sourceBody865_324

def sourceBody865_326 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_305 sourceBody865_325

def sourceBody865_327 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_0 sourceBody865_326

def sourceBody865_328 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_304 sourceBody865_327

def sourceBody865_329 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_0 sourceBody865_328

def sourceBody865_330 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_303 sourceBody865_329

def sourceBody865_331 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_0 sourceBody865_330

def sourceBody865_332 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_302 sourceBody865_331

def sourceBody865_333 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_0 sourceBody865_332

def sourceBody865_334 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_301 sourceBody865_333

def sourceBody865_335 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_0 sourceBody865_334

def sourceBody865_336 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_300 sourceBody865_335

def sourceBody865_337 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 408#64]),
      Flapjack.WordLangExpHOL.const 80#64])

def sourceBody865_338 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 120#64]))

def sourceBody865_339 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_338 sourceBody865_260

def sourceBody865_340 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_0 sourceBody865_339

def sourceBody865_341 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_337 sourceBody865_340

def sourceBody865_342 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_0 sourceBody865_341

def sourceBody865_343 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_336 sourceBody865_342

def sourceBody865_344 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 408#64]),
      Flapjack.WordLangExpHOL.const 88#64])

def sourceBody865_345 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 144#64]))

def sourceBody865_346 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_345 sourceBody865_260

def sourceBody865_347 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_0 sourceBody865_346

def sourceBody865_348 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_344 sourceBody865_347

def sourceBody865_349 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_0 sourceBody865_348

def sourceBody865_350 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_343 sourceBody865_349

def sourceBody865_351 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 408#64]),
      Flapjack.WordLangExpHOL.const 96#64])

def sourceBody865_352 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 208#64]))

def sourceBody865_353 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_352 sourceBody865_260

def sourceBody865_354 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_0 sourceBody865_353

def sourceBody865_355 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_351 sourceBody865_354

def sourceBody865_356 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_0 sourceBody865_355

def sourceBody865_357 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_350 sourceBody865_356

def sourceBody865_358 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 408#64]),
      Flapjack.WordLangExpHOL.const 104#64])

def sourceBody865_359 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 216#64]))

def sourceBody865_360 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_359 sourceBody865_260

def sourceBody865_361 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_0 sourceBody865_360

def sourceBody865_362 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_358 sourceBody865_361

def sourceBody865_363 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_0 sourceBody865_362

def sourceBody865_364 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_357 sourceBody865_363

def sourceBody865_365 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 408#64]),
      Flapjack.WordLangExpHOL.const 112#64])

def sourceBody865_366 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 240#64]))

def sourceBody865_367 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_366 sourceBody865_260

def sourceBody865_368 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_0 sourceBody865_367

def sourceBody865_369 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_365 sourceBody865_368

def sourceBody865_370 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_0 sourceBody865_369

def sourceBody865_371 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_364 sourceBody865_370

def sourceBody865_372 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 2)

def sourceBody865_373 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody865_0, 865, 26)) (some 864) ([24, 16]) (some (24, sourceBody865_216, 865, 27))

def sourceBody865_374 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_373 sourceBody865_6

def sourceBody865_375 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_374 sourceBody865_0

def sourceBody865_376 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_215 sourceBody865_375

def sourceBody865_377 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_372 sourceBody865_376

def sourceBody865_378 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_0 sourceBody865_377

def sourceBody865_379 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_0 sourceBody865_378

def sourceBody865_380 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_371 sourceBody865_379

def sourceBody865_381 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [4]

def sourceBody865_382 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_381 sourceBody865_0

def sourceBody865_383 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_166 sourceBody865_382

def sourceBody865_384 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_380 sourceBody865_383

def sourceBody865_385 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_191 sourceBody865_384

def sourceBody865_386 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_0 sourceBody865_385

def sourceBody865_387 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_0 sourceBody865_386

def sourceBody865_388 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_185 sourceBody865_387

def sourceBody865_389 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_162 sourceBody865_388

def sourceBody865_390 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_0 sourceBody865_389

def sourceBody865_391 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_0 sourceBody865_390

def sourceBody865_392 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_154 sourceBody865_391

def sourceBody865_393 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_144 sourceBody865_392

def sourceBody865_394 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_0 sourceBody865_393

def sourceBody865_395 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_0 sourceBody865_394

def sourceBody865_396 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_138 sourceBody865_395

def sourceBody865_397 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_0 sourceBody865_396

def sourceBody865_398 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_0 sourceBody865_397

def sourceBody865_399 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_132 sourceBody865_398

def sourceBody865_400 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_85 sourceBody865_399

def sourceBody865_401 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_0 sourceBody865_400

def sourceBody865_402 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_84 sourceBody865_401

def sourceBody865_403 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_0 sourceBody865_402

def sourceBody865_404 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_83 sourceBody865_403

def sourceBody865_405 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_0 sourceBody865_404

def sourceBody865_406 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_82 sourceBody865_405

def sourceBody865_407 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_70 sourceBody865_406

def sourceBody865_408 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_0 sourceBody865_407

def sourceBody865_409 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_0 sourceBody865_408

def sourceBody865_410 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_62 sourceBody865_409

def sourceBody865_411 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_0 sourceBody865_410

def sourceBody865_412 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_0 sourceBody865_411

def sourceBody865_413 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_54 sourceBody865_412

def sourceBody865_414 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_36 sourceBody865_413

def sourceBody865_415 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_0 sourceBody865_414

def sourceBody865_416 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_35 sourceBody865_415

def sourceBody865_417 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_11 sourceBody865_416

def sourceBody865_418 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_0 sourceBody865_417

def sourceBody865_419 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_10 sourceBody865_418

def sourceBody865_420 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_0 sourceBody865_419

def sourceBody865_421 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_0 sourceBody865_420

def sourceBody865_422 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_0 sourceBody865_421

def sourceBody865_423 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_0 sourceBody865_422

def sourceBody865_424 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_1 sourceBody865_423

def sourceBody865_425 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody865_0 sourceBody865_424

def source865 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (865, 2, sourceBody865_425)
end InitECandidate.Proofs.WordStages
