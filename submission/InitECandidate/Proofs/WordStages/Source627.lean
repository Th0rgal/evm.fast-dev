import InitECandidate.Proofs.WordStages.Source611
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody627_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody627_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 336#64]))

def sourceBody627_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 1732584193#64)

def sourceBody627_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 18)

def sourceBody627_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 10) 14

def sourceBody627_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_4 sourceBody627_0

def sourceBody627_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_3 sourceBody627_5

def sourceBody627_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_6 sourceBody627_0

def sourceBody627_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_2 sourceBody627_7

def sourceBody627_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_0 sourceBody627_8

def sourceBody627_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_1 sourceBody627_9

def sourceBody627_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_0 sourceBody627_10

def sourceBody627_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 336#64]),
      Flapjack.WordLangExpHOL.const 8#64])

def sourceBody627_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 4023233417#64)

def sourceBody627_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_13 sourceBody627_7

def sourceBody627_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_0 sourceBody627_14

def sourceBody627_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_12 sourceBody627_15

def sourceBody627_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_0 sourceBody627_16

def sourceBody627_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_11 sourceBody627_17

def sourceBody627_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 336#64]),
      Flapjack.WordLangExpHOL.const 16#64])

def sourceBody627_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 2562383102#64)

def sourceBody627_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_20 sourceBody627_7

def sourceBody627_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_0 sourceBody627_21

def sourceBody627_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_19 sourceBody627_22

def sourceBody627_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_0 sourceBody627_23

def sourceBody627_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_18 sourceBody627_24

def sourceBody627_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 336#64]),
      Flapjack.WordLangExpHOL.const 24#64])

def sourceBody627_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 271733878#64)

def sourceBody627_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_27 sourceBody627_7

def sourceBody627_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_0 sourceBody627_28

def sourceBody627_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_26 sourceBody627_29

def sourceBody627_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_0 sourceBody627_30

def sourceBody627_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_25 sourceBody627_31

def sourceBody627_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 336#64]),
      Flapjack.WordLangExpHOL.const 32#64])

def sourceBody627_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 3285377520#64)

def sourceBody627_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_34 sourceBody627_7

def sourceBody627_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_0 sourceBody627_35

def sourceBody627_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_33 sourceBody627_36

def sourceBody627_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_0 sourceBody627_37

def sourceBody627_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_32 sourceBody627_38

def sourceBody627_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody627_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody627_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 4)

def sourceBody627_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 64#64])

def sourceBody627_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody627_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody627_46 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notLower) 14 (Flapjack.WordRegImm.reg 20) sourceBody627_44 sourceBody627_45

def sourceBody627_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_46 sourceBody627_41

def sourceBody627_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 14)

def sourceBody627_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 336#64]))

def sourceBody627_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.var 10])

def sourceBody627_51 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody627_52 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody627_0, 627, 2)) (some 626) ([14, 20]) (some (14, sourceBody627_51, 627, 3))

def sourceBody627_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_52 sourceBody627_41

def sourceBody627_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_53 sourceBody627_0

def sourceBody627_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_50 sourceBody627_54

def sourceBody627_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_49 sourceBody627_55

def sourceBody627_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_0 sourceBody627_56

def sourceBody627_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_0 sourceBody627_57

def sourceBody627_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 64#64])

def sourceBody627_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 18)

def sourceBody627_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_60 sourceBody627_0

def sourceBody627_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_61 sourceBody627_0

def sourceBody627_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_59 sourceBody627_62

def sourceBody627_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_0 sourceBody627_63

def sourceBody627_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_58 sourceBody627_64

def sourceBody627_66 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody627_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_65 sourceBody627_66

def sourceBody627_68 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody627_69 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.WordRegImm.imm 0#64) sourceBody627_67 sourceBody627_68

def sourceBody627_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_69 sourceBody627_41

def sourceBody627_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_70 sourceBody627_0

def sourceBody627_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_48 sourceBody627_71

def sourceBody627_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_47 sourceBody627_72

def sourceBody627_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_43 sourceBody627_73

def sourceBody627_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_42 sourceBody627_74

def sourceBody627_76 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.ls PUnit.unit))
  PUnit.unit Flapjack.Spt.ln) sourceBody627_75 (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.ls PUnit.unit))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody627_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_76 sourceBody627_41

def sourceBody627_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_41 sourceBody627_77

def sourceBody627_79 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.var 10])

def sourceBody627_80 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 344#64]))

def sourceBody627_81 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 128#64)

def sourceBody627_82 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody627_83 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody627_0, 627, 4)) (some 78) ([20, 8]) (some (20, sourceBody627_82, 627, 5))

def sourceBody627_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_83 sourceBody627_41

def sourceBody627_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_84 sourceBody627_0

def sourceBody627_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_81 sourceBody627_85

def sourceBody627_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_80 sourceBody627_86

def sourceBody627_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_0 sourceBody627_87

def sourceBody627_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_0 sourceBody627_88

def sourceBody627_90 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.var 10])

def sourceBody627_91 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 18)

def sourceBody627_92 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody627_0, 627, 6)) (some 77) ([20, 8, 16]) (some (20, sourceBody627_82, 627, 7))

def sourceBody627_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_92 sourceBody627_41

def sourceBody627_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_93 sourceBody627_0

def sourceBody627_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_91 sourceBody627_94

def sourceBody627_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_90 sourceBody627_95

def sourceBody627_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_80 sourceBody627_96

def sourceBody627_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_0 sourceBody627_97

def sourceBody627_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_0 sourceBody627_98

def sourceBody627_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_89 sourceBody627_99

def sourceBody627_101 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 344#64]),
      Flapjack.WordLangExpHOL.var 18])

def sourceBody627_102 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 128#64)

def sourceBody627_103 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.store8 20 (Flapjack.WordLangAddr.addr 14 0#64))

def sourceBody627_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_103 sourceBody627_0

def sourceBody627_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_102 sourceBody627_104

def sourceBody627_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_101 sourceBody627_105

def sourceBody627_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_100 sourceBody627_106

def sourceBody627_108 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 64#64)

def sourceBody627_109 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 18)

def sourceBody627_110 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 56#64)

def sourceBody627_111 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody627_112 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody627_113 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notLower) 8 (Flapjack.WordRegImm.reg 16) sourceBody627_111 sourceBody627_112

def sourceBody627_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_113 sourceBody627_41

def sourceBody627_115 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 8)

def sourceBody627_116 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 128#64)

def sourceBody627_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_116 sourceBody627_0

def sourceBody627_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_117 sourceBody627_0

def sourceBody627_119 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.imm 0#64) sourceBody627_118 sourceBody627_0

def sourceBody627_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_119 sourceBody627_41

def sourceBody627_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_120 sourceBody627_0

def sourceBody627_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_115 sourceBody627_121

def sourceBody627_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_114 sourceBody627_122

def sourceBody627_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_110 sourceBody627_123

def sourceBody627_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_109 sourceBody627_124

def sourceBody627_126 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
        [Flapjack.WordLangExpHOL.load
            (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
              [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                  [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                    Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                      (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                      (Flapjack.WordLangExpHOL.const 1#64)],
                Flapjack.WordLangExpHOL.const 344#64]),
          Flapjack.WordLangExpHOL.var 14],
      Flapjack.WordLangExpHOL.const 8#64])

def sourceBody627_127 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 4)
    (Flapjack.WordLangExpHOL.const 3#64))

def sourceBody627_128 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody627_129 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody627_0, 627, 8)) (some 87) ([8, 16]) (some (8, sourceBody627_128, 627, 9))

def sourceBody627_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_129 sourceBody627_41

def sourceBody627_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_130 sourceBody627_0

def sourceBody627_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_127 sourceBody627_131

def sourceBody627_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_126 sourceBody627_132

def sourceBody627_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_0 sourceBody627_133

def sourceBody627_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_0 sourceBody627_134

def sourceBody627_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_125 sourceBody627_135

def sourceBody627_137 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 336#64]))

def sourceBody627_138 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 344#64]))

def sourceBody627_139 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody627_0, 627, 10)) (some 626) ([8, 16]) (some (8, sourceBody627_128, 627, 11))

def sourceBody627_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_139 sourceBody627_41

def sourceBody627_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_140 sourceBody627_0

def sourceBody627_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_138 sourceBody627_141

def sourceBody627_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_137 sourceBody627_142

def sourceBody627_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_0 sourceBody627_143

def sourceBody627_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_0 sourceBody627_144

def sourceBody627_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_136 sourceBody627_145

def sourceBody627_147 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 128#64)

def sourceBody627_148 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 8 (Flapjack.WordRegImm.reg 16) sourceBody627_111 sourceBody627_112

def sourceBody627_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_148 sourceBody627_41

def sourceBody627_150 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 344#64]),
      Flapjack.WordLangExpHOL.const 64#64])

def sourceBody627_151 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody627_0, 627, 12)) (some 626) ([8, 16]) (some (8, sourceBody627_128, 627, 13))

def sourceBody627_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_151 sourceBody627_41

def sourceBody627_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_152 sourceBody627_0

def sourceBody627_154 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_150 sourceBody627_153

def sourceBody627_155 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_137 sourceBody627_154

def sourceBody627_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_0 sourceBody627_155

def sourceBody627_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_0 sourceBody627_156

def sourceBody627_158 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.imm 0#64) sourceBody627_157 sourceBody627_0

def sourceBody627_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_158 sourceBody627_41

def sourceBody627_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_159 sourceBody627_0

def sourceBody627_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_115 sourceBody627_160

def sourceBody627_162 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_149 sourceBody627_161

def sourceBody627_163 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_147 sourceBody627_162

def sourceBody627_164 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_48 sourceBody627_163

def sourceBody627_165 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_146 sourceBody627_164

def sourceBody627_166 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_40 sourceBody627_0

def sourceBody627_167 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_166 sourceBody627_0

def sourceBody627_168 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_165 sourceBody627_167

def sourceBody627_169 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 10)

def sourceBody627_170 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 5#64)

def sourceBody627_171 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.less) 8 (Flapjack.WordRegImm.reg 16) sourceBody627_111 sourceBody627_112

def sourceBody627_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_171 sourceBody627_41

def sourceBody627_173 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 6,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 10)
        (Flapjack.WordLangExpHOL.const 2#64)])

def sourceBody627_174 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.load
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
            [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                  Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                    (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                    (Flapjack.WordLangExpHOL.const 1#64)],
              Flapjack.WordLangExpHOL.const 336#64]),
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 10)
          (Flapjack.WordLangExpHOL.const 3#64)]))

def sourceBody627_175 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody627_0, 627, 14)) (some 86) ([8, 16]) (some (8, sourceBody627_128, 627, 15))

def sourceBody627_176 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_175 sourceBody627_41

def sourceBody627_177 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_176 sourceBody627_0

def sourceBody627_178 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_174 sourceBody627_177

def sourceBody627_179 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_173 sourceBody627_178

def sourceBody627_180 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_0 sourceBody627_179

def sourceBody627_181 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_0 sourceBody627_180

def sourceBody627_182 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody627_183 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 20)

def sourceBody627_184 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_183 sourceBody627_0

def sourceBody627_185 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_184 sourceBody627_0

def sourceBody627_186 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_182 sourceBody627_185

def sourceBody627_187 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_0 sourceBody627_186

def sourceBody627_188 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_181 sourceBody627_187

def sourceBody627_189 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_188 sourceBody627_66

def sourceBody627_190 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.imm 0#64) sourceBody627_189 sourceBody627_68

def sourceBody627_191 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_190 sourceBody627_41

def sourceBody627_192 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_191 sourceBody627_0

def sourceBody627_193 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_115 sourceBody627_192

def sourceBody627_194 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_172 sourceBody627_193

def sourceBody627_195 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_170 sourceBody627_194

def sourceBody627_196 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_169 sourceBody627_195

def sourceBody627_197 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  PUnit.unit Flapjack.Spt.ln) sourceBody627_196 (Flapjack.Spt.ls PUnit.unit)

def sourceBody627_198 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_197 sourceBody627_41

def sourceBody627_199 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_41 sourceBody627_198

def sourceBody627_200 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_168 sourceBody627_199

def sourceBody627_201 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody627_202 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [20]

def sourceBody627_203 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_202 sourceBody627_0

def sourceBody627_204 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_201 sourceBody627_203

def sourceBody627_205 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_200 sourceBody627_204

def sourceBody627_206 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_108 sourceBody627_205

def sourceBody627_207 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_0 sourceBody627_206

def sourceBody627_208 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_107 sourceBody627_207

def sourceBody627_209 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_79 sourceBody627_208

def sourceBody627_210 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_0 sourceBody627_209

def sourceBody627_211 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_78 sourceBody627_210

def sourceBody627_212 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_40 sourceBody627_211

def sourceBody627_213 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_0 sourceBody627_212

def sourceBody627_214 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody627_39 sourceBody627_213

def source627 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (627, 4, sourceBody627_214)
end InitECandidate.Proofs.WordStages
