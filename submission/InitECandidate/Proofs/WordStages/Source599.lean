import InitECandidate.Proofs.WordStages.Source583
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody599_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody599_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody599_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 4)

def sourceBody599_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 2#64)

def sourceBody599_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody599_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody599_6 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 26 (Flapjack.WordRegImm.reg 18) sourceBody599_4 sourceBody599_5

def sourceBody599_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody599_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_6 sourceBody599_7

def sourceBody599_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 26)

def sourceBody599_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody599_11 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody599_0, 599, 2)) (some 386) ([]) (some (20, sourceBody599_10, 599, 3))

def sourceBody599_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_11 sourceBody599_7

def sourceBody599_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_12 sourceBody599_0

def sourceBody599_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 32#64]))

def sourceBody599_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 20)

def sourceBody599_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody599_17 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody599_0, 599, 4)) (some 417) ([18]) (some (18, sourceBody599_16, 599, 5))

def sourceBody599_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_17 sourceBody599_7

def sourceBody599_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_18 sourceBody599_0

def sourceBody599_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_15 sourceBody599_19

def sourceBody599_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_0 sourceBody599_20

def sourceBody599_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_0 sourceBody599_21

def sourceBody599_23 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody599_0, 599, 6)) (some 421) ([18]) (some (18, sourceBody599_16, 599, 7))

def sourceBody599_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_23 sourceBody599_7

def sourceBody599_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_24 sourceBody599_0

def sourceBody599_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_15 sourceBody599_25

def sourceBody599_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_0 sourceBody599_26

def sourceBody599_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_0 sourceBody599_27

def sourceBody599_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_22 sourceBody599_28

def sourceBody599_30 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody599_0, 599, 8)) (some 426) ([18]) (some (18, sourceBody599_16, 599, 9))

def sourceBody599_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_30 sourceBody599_7

def sourceBody599_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_31 sourceBody599_0

def sourceBody599_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_15 sourceBody599_32

def sourceBody599_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_0 sourceBody599_33

def sourceBody599_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_0 sourceBody599_34

def sourceBody599_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_29 sourceBody599_35

def sourceBody599_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_14 sourceBody599_36

def sourceBody599_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_0 sourceBody599_37

def sourceBody599_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_13 sourceBody599_38

def sourceBody599_40 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 24 (Flapjack.WordRegImm.imm 0#64) sourceBody599_39 sourceBody599_0

def sourceBody599_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_40 sourceBody599_7

def sourceBody599_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_41 sourceBody599_0

def sourceBody599_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_9 sourceBody599_42

def sourceBody599_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_8 sourceBody599_43

def sourceBody599_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_3 sourceBody599_44

def sourceBody599_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_2 sourceBody599_45

def sourceBody599_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 1024#64)

def sourceBody599_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 128#64]))

def sourceBody599_49 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 26 (Flapjack.WordRegImm.reg 18) sourceBody599_4 sourceBody599_5

def sourceBody599_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_49 sourceBody599_7

def sourceBody599_51 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 7#64)

def sourceBody599_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 20)

def sourceBody599_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_52 sourceBody599_0

def sourceBody599_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_53 sourceBody599_0

def sourceBody599_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_51 sourceBody599_54

def sourceBody599_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_0 sourceBody599_55

def sourceBody599_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 8#64)

def sourceBody599_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_57 sourceBody599_10

def sourceBody599_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_56 sourceBody599_58

def sourceBody599_60 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 24 (Flapjack.WordRegImm.imm 0#64) sourceBody599_59 sourceBody599_0

def sourceBody599_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_60 sourceBody599_7

def sourceBody599_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_61 sourceBody599_0

def sourceBody599_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_9 sourceBody599_62

def sourceBody599_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_50 sourceBody599_63

def sourceBody599_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_48 sourceBody599_64

def sourceBody599_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_47 sourceBody599_65

def sourceBody599_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_46 sourceBody599_66

def sourceBody599_68 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 2)

def sourceBody599_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 4)

def sourceBody599_70 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 26

def sourceBody599_71 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody599_0, 599, 10)) (some 592) ([26, 18]) (some (26, sourceBody599_70, 599, 11))

def sourceBody599_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_71 sourceBody599_7

def sourceBody599_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_72 sourceBody599_0

def sourceBody599_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_69 sourceBody599_73

def sourceBody599_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_68 sourceBody599_74

def sourceBody599_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_0 sourceBody599_75

def sourceBody599_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_0 sourceBody599_76

def sourceBody599_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_67 sourceBody599_77

def sourceBody599_79 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody599_0, 599, 12)) (some 386) ([]) (some (26, sourceBody599_70, 599, 13))

def sourceBody599_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_79 sourceBody599_7

def sourceBody599_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_80 sourceBody599_0

def sourceBody599_82 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 288#64]),
      Flapjack.WordLangExpHOL.const 24#64])

def sourceBody599_83 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 18)

def sourceBody599_84 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 26) 24

def sourceBody599_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_84 sourceBody599_0

def sourceBody599_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_83 sourceBody599_85

def sourceBody599_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_86 sourceBody599_0

def sourceBody599_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_15 sourceBody599_87

def sourceBody599_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_0 sourceBody599_88

def sourceBody599_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_82 sourceBody599_89

def sourceBody599_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_0 sourceBody599_90

def sourceBody599_92 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 288#64]),
      Flapjack.WordLangExpHOL.const 96#64])

def sourceBody599_93 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 22)

def sourceBody599_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_93 sourceBody599_87

def sourceBody599_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_0 sourceBody599_94

def sourceBody599_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_92 sourceBody599_95

def sourceBody599_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_0 sourceBody599_96

def sourceBody599_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_91 sourceBody599_97

def sourceBody599_99 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 288#64]),
      Flapjack.WordLangExpHOL.const 48#64])

def sourceBody599_100 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 6)

def sourceBody599_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_100 sourceBody599_87

def sourceBody599_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_0 sourceBody599_101

def sourceBody599_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_99 sourceBody599_102

def sourceBody599_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_0 sourceBody599_103

def sourceBody599_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_98 sourceBody599_104

def sourceBody599_106 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 288#64]),
      Flapjack.WordLangExpHOL.const 56#64])

def sourceBody599_107 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 8)

def sourceBody599_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_107 sourceBody599_87

def sourceBody599_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_0 sourceBody599_108

def sourceBody599_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_106 sourceBody599_109

def sourceBody599_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_0 sourceBody599_110

def sourceBody599_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_105 sourceBody599_111

def sourceBody599_113 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 288#64]),
      Flapjack.WordLangExpHOL.const 64#64])

def sourceBody599_114 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 10)

def sourceBody599_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_114 sourceBody599_87

def sourceBody599_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_0 sourceBody599_115

def sourceBody599_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_113 sourceBody599_116

def sourceBody599_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_0 sourceBody599_117

def sourceBody599_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_112 sourceBody599_118

def sourceBody599_120 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 288#64]),
      Flapjack.WordLangExpHOL.const 72#64])

def sourceBody599_121 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 12)

def sourceBody599_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_121 sourceBody599_87

def sourceBody599_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_0 sourceBody599_122

def sourceBody599_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_120 sourceBody599_123

def sourceBody599_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_0 sourceBody599_124

def sourceBody599_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_119 sourceBody599_125

def sourceBody599_127 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 288#64]),
      Flapjack.WordLangExpHOL.const 80#64])

def sourceBody599_128 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 14)

def sourceBody599_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_128 sourceBody599_87

def sourceBody599_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_0 sourceBody599_129

def sourceBody599_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_127 sourceBody599_130

def sourceBody599_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_0 sourceBody599_131

def sourceBody599_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_126 sourceBody599_132

def sourceBody599_134 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 288#64]),
      Flapjack.WordLangExpHOL.const 88#64])

def sourceBody599_135 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 16)

def sourceBody599_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_135 sourceBody599_87

def sourceBody599_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_0 sourceBody599_136

def sourceBody599_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_134 sourceBody599_137

def sourceBody599_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_0 sourceBody599_138

def sourceBody599_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_133 sourceBody599_139

def sourceBody599_141 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody599_0, 599, 14)) (some 595) ([]) (some (18, sourceBody599_16, 599, 15))

def sourceBody599_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_141 sourceBody599_7

def sourceBody599_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_142 sourceBody599_0

def sourceBody599_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_0 sourceBody599_143

def sourceBody599_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_0 sourceBody599_144

def sourceBody599_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_140 sourceBody599_145

def sourceBody599_147 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [26]

def sourceBody599_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_147 sourceBody599_0

def sourceBody599_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_5 sourceBody599_148

def sourceBody599_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_146 sourceBody599_149

def sourceBody599_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_81 sourceBody599_150

def sourceBody599_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_0 sourceBody599_151

def sourceBody599_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_0 sourceBody599_152

def sourceBody599_154 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_78 sourceBody599_153

def sourceBody599_155 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_1 sourceBody599_154

def sourceBody599_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody599_0 sourceBody599_155

def source599 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (599, 9, sourceBody599_156)
end InitECandidate.Proofs.WordStages
