import InitECandidate.Proofs.WordStages.Source832
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody848_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody848_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody848_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody848_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody848_0, 848, 2)) (some 68) ([10]) (some (10, sourceBody848_2, 848, 3))

def sourceBody848_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody848_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_3 sourceBody848_4

def sourceBody848_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_5 sourceBody848_0

def sourceBody848_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_1 sourceBody848_6

def sourceBody848_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
        [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
          Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
            (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
      Flapjack.WordLangExpHOL.const 432#64])

def sourceBody848_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 4)

def sourceBody848_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 2)

def sourceBody848_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 10) 8

def sourceBody848_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_11 sourceBody848_0

def sourceBody848_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_10 sourceBody848_12

def sourceBody848_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_13 sourceBody848_0

def sourceBody848_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_9 sourceBody848_14

def sourceBody848_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_0 sourceBody848_15

def sourceBody848_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_8 sourceBody848_16

def sourceBody848_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_0 sourceBody848_17

def sourceBody848_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_7 sourceBody848_18

def sourceBody848_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_0 sourceBody848_19

def sourceBody848_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_0 sourceBody848_20

def sourceBody848_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 432#64]))

def sourceBody848_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody848_24 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody848_0, 848, 4)) (some 78) ([10, 2]) (some (10, sourceBody848_2, 848, 5))

def sourceBody848_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_24 sourceBody848_4

def sourceBody848_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_25 sourceBody848_0

def sourceBody848_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_23 sourceBody848_26

def sourceBody848_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_22 sourceBody848_27

def sourceBody848_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_0 sourceBody848_28

def sourceBody848_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_0 sourceBody848_29

def sourceBody848_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_21 sourceBody848_30

def sourceBody848_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 360#64)

def sourceBody848_33 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody848_0, 848, 6)) (some 68) ([10]) (some (10, sourceBody848_2, 848, 7))

def sourceBody848_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_33 sourceBody848_4

def sourceBody848_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_34 sourceBody848_0

def sourceBody848_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_32 sourceBody848_35

def sourceBody848_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
        [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
          Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
            (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
      Flapjack.WordLangExpHOL.const 424#64])

def sourceBody848_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_37 sourceBody848_16

def sourceBody848_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_0 sourceBody848_38

def sourceBody848_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_36 sourceBody848_39

def sourceBody848_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_0 sourceBody848_40

def sourceBody848_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_0 sourceBody848_41

def sourceBody848_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_31 sourceBody848_42

def sourceBody848_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 424#64]))

def sourceBody848_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 360#64)

def sourceBody848_46 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody848_0, 848, 8)) (some 78) ([10, 2]) (some (10, sourceBody848_2, 848, 9))

def sourceBody848_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_46 sourceBody848_4

def sourceBody848_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_47 sourceBody848_0

def sourceBody848_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_45 sourceBody848_48

def sourceBody848_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_44 sourceBody848_49

def sourceBody848_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_0 sourceBody848_50

def sourceBody848_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_0 sourceBody848_51

def sourceBody848_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_43 sourceBody848_52

def sourceBody848_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody848_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 17#64)

def sourceBody848_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody848_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody848_58 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.less) 2 (Flapjack.WordRegImm.reg 8) sourceBody848_56 sourceBody848_57

def sourceBody848_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_58 sourceBody848_4

def sourceBody848_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 2)

def sourceBody848_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 4)

def sourceBody848_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 20#64)

def sourceBody848_63 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.longMul 8 8 10 2))

def sourceBody848_64 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 424#64]),
      Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 19#64])

def sourceBody848_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody848_66 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.store8 12 (Flapjack.WordLangAddr.addr 6 0#64))

def sourceBody848_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_66 sourceBody848_0

def sourceBody848_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_65 sourceBody848_67

def sourceBody848_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_64 sourceBody848_68

def sourceBody848_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_63 sourceBody848_69

def sourceBody848_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_62 sourceBody848_70

def sourceBody848_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_61 sourceBody848_71

def sourceBody848_73 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody848_74 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 10)

def sourceBody848_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_74 sourceBody848_0

def sourceBody848_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_75 sourceBody848_0

def sourceBody848_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_73 sourceBody848_76

def sourceBody848_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_0 sourceBody848_77

def sourceBody848_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_72 sourceBody848_78

def sourceBody848_80 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody848_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_79 sourceBody848_80

def sourceBody848_82 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody848_83 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.WordRegImm.imm 0#64) sourceBody848_81 sourceBody848_82

def sourceBody848_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_83 sourceBody848_4

def sourceBody848_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_84 sourceBody848_0

def sourceBody848_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_60 sourceBody848_85

def sourceBody848_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_59 sourceBody848_86

def sourceBody848_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_55 sourceBody848_87

def sourceBody848_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_9 sourceBody848_88

def sourceBody848_90 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln) sourceBody848_89 (Flapjack.Spt.ls PUnit.unit)

def sourceBody848_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_90 sourceBody848_4

def sourceBody848_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_4 sourceBody848_91

def sourceBody848_93 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 424#64]),
      Flapjack.WordLangExpHOL.const 340#64, Flapjack.WordLangExpHOL.const 18#64])

def sourceBody848_94 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.store8 2 (Flapjack.WordLangAddr.addr 10 0#64))

def sourceBody848_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_94 sourceBody848_0

def sourceBody848_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_56 sourceBody848_95

def sourceBody848_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_93 sourceBody848_96

def sourceBody848_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_92 sourceBody848_97

def sourceBody848_99 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 24#64)

def sourceBody848_100 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 2

def sourceBody848_101 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody848_0, 848, 10)) (some 68) ([2]) (some (2, sourceBody848_100, 848, 11))

def sourceBody848_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_101 sourceBody848_4

def sourceBody848_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_102 sourceBody848_0

def sourceBody848_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_99 sourceBody848_103

def sourceBody848_105 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
        [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
          Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
            (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
      Flapjack.WordLangExpHOL.const 464#64])

def sourceBody848_106 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 10)

def sourceBody848_107 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 8)

def sourceBody848_108 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 2) 6

def sourceBody848_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_108 sourceBody848_0

def sourceBody848_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_107 sourceBody848_109

def sourceBody848_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_110 sourceBody848_0

def sourceBody848_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_106 sourceBody848_111

def sourceBody848_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_0 sourceBody848_112

def sourceBody848_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_105 sourceBody848_113

def sourceBody848_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_0 sourceBody848_114

def sourceBody848_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_104 sourceBody848_115

def sourceBody848_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_0 sourceBody848_116

def sourceBody848_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_0 sourceBody848_117

def sourceBody848_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_98 sourceBody848_118

def sourceBody848_120 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 464#64]))

def sourceBody848_121 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 998902#64)

def sourceBody848_122 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 15506597749690834871#64)

def sourceBody848_123 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 13311379508201171970#64)

def sourceBody848_124 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody848_0, 848, 12)) (some 847) ([2, 8, 6, 12]) (some (2, sourceBody848_100, 848, 13))

def sourceBody848_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_124 sourceBody848_4

def sourceBody848_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_125 sourceBody848_0

def sourceBody848_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_123 sourceBody848_126

def sourceBody848_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_122 sourceBody848_127

def sourceBody848_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_121 sourceBody848_128

def sourceBody848_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_120 sourceBody848_129

def sourceBody848_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_0 sourceBody848_130

def sourceBody848_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_0 sourceBody848_131

def sourceBody848_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_119 sourceBody848_132

def sourceBody848_134 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody848_0, 848, 14)) (some 68) ([2]) (some (2, sourceBody848_100, 848, 15))

def sourceBody848_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_134 sourceBody848_4

def sourceBody848_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_135 sourceBody848_0

def sourceBody848_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_99 sourceBody848_136

def sourceBody848_138 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
        [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
          Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
            (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
      Flapjack.WordLangExpHOL.const 472#64])

def sourceBody848_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_138 sourceBody848_113

def sourceBody848_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_0 sourceBody848_139

def sourceBody848_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_137 sourceBody848_140

def sourceBody848_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_0 sourceBody848_141

def sourceBody848_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_0 sourceBody848_142

def sourceBody848_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_133 sourceBody848_143

def sourceBody848_145 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 472#64]))

def sourceBody848_146 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 63752#64)

def sourceBody848_147 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 2878298490047003138#64)

def sourceBody848_148 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 3700577164601600309#64)

def sourceBody848_149 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody848_0, 848, 16)) (some 847) ([2, 8, 6, 12]) (some (2, sourceBody848_100, 848, 17))

def sourceBody848_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_149 sourceBody848_4

def sourceBody848_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_150 sourceBody848_0

def sourceBody848_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_148 sourceBody848_151

def sourceBody848_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_147 sourceBody848_152

def sourceBody848_154 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_146 sourceBody848_153

def sourceBody848_155 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_145 sourceBody848_154

def sourceBody848_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_0 sourceBody848_155

def sourceBody848_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_0 sourceBody848_156

def sourceBody848_158 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_144 sourceBody848_157

def sourceBody848_159 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody848_0, 848, 18)) (some 68) ([2]) (some (2, sourceBody848_100, 848, 19))

def sourceBody848_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_159 sourceBody848_4

def sourceBody848_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_160 sourceBody848_0

def sourceBody848_162 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_99 sourceBody848_161

def sourceBody848_163 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
        [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
          Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
            (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
      Flapjack.WordLangExpHOL.const 480#64])

def sourceBody848_164 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_163 sourceBody848_113

def sourceBody848_165 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_0 sourceBody848_164

def sourceBody848_166 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_162 sourceBody848_165

def sourceBody848_167 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_0 sourceBody848_166

def sourceBody848_168 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_0 sourceBody848_167

def sourceBody848_169 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_158 sourceBody848_168

def sourceBody848_170 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 480#64]))

def sourceBody848_171 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 2401#64)

def sourceBody848_172 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 17242047345525313946#64)

def sourceBody848_173 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 15579492241104728066#64)

def sourceBody848_174 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody848_0, 848, 20)) (some 847) ([2, 8, 6, 12]) (some (2, sourceBody848_100, 848, 21))

def sourceBody848_175 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_174 sourceBody848_4

def sourceBody848_176 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_175 sourceBody848_0

def sourceBody848_177 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_173 sourceBody848_176

def sourceBody848_178 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_172 sourceBody848_177

def sourceBody848_179 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_171 sourceBody848_178

def sourceBody848_180 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_170 sourceBody848_179

def sourceBody848_181 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_0 sourceBody848_180

def sourceBody848_182 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_0 sourceBody848_181

def sourceBody848_183 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_169 sourceBody848_182

def sourceBody848_184 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody848_0, 848, 22)) (some 68) ([2]) (some (2, sourceBody848_100, 848, 23))

def sourceBody848_185 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_184 sourceBody848_4

def sourceBody848_186 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_185 sourceBody848_0

def sourceBody848_187 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_99 sourceBody848_186

def sourceBody848_188 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
        [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
          Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
            (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
      Flapjack.WordLangExpHOL.const 488#64])

def sourceBody848_189 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_188 sourceBody848_113

def sourceBody848_190 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_0 sourceBody848_189

def sourceBody848_191 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_187 sourceBody848_190

def sourceBody848_192 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_0 sourceBody848_191

def sourceBody848_193 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_0 sourceBody848_192

def sourceBody848_194 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_183 sourceBody848_193

def sourceBody848_195 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 488#64]))

def sourceBody848_196 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 48093#64)

def sourceBody848_197 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 14397524800236640159#64)

def sourceBody848_198 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 10016273463683084881#64)

def sourceBody848_199 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody848_0, 848, 24)) (some 847) ([2, 8, 6, 12]) (some (2, sourceBody848_100, 848, 25))

def sourceBody848_200 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_199 sourceBody848_4

def sourceBody848_201 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_200 sourceBody848_0

def sourceBody848_202 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_198 sourceBody848_201

def sourceBody848_203 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_197 sourceBody848_202

def sourceBody848_204 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_196 sourceBody848_203

def sourceBody848_205 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_195 sourceBody848_204

def sourceBody848_206 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_0 sourceBody848_205

def sourceBody848_207 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_0 sourceBody848_206

def sourceBody848_208 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_194 sourceBody848_207

def sourceBody848_209 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody848_0, 848, 26)) (some 68) ([2]) (some (2, sourceBody848_100, 848, 27))

def sourceBody848_210 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_209 sourceBody848_4

def sourceBody848_211 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_210 sourceBody848_0

def sourceBody848_212 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_99 sourceBody848_211

def sourceBody848_213 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
        [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
          Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
            (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
      Flapjack.WordLangExpHOL.const 496#64])

def sourceBody848_214 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_213 sourceBody848_113

def sourceBody848_215 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_0 sourceBody848_214

def sourceBody848_216 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_212 sourceBody848_215

def sourceBody848_217 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_0 sourceBody848_216

def sourceBody848_218 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_0 sourceBody848_217

def sourceBody848_219 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_208 sourceBody848_218

def sourceBody848_220 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 496#64]))

def sourceBody848_221 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 49140#64)

def sourceBody848_222 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 7603452151126424148#64)

def sourceBody848_223 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 760111669195932290#64)

def sourceBody848_224 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody848_0, 848, 28)) (some 847) ([2, 8, 6, 12]) (some (2, sourceBody848_100, 848, 29))

def sourceBody848_225 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_224 sourceBody848_4

def sourceBody848_226 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_225 sourceBody848_0

def sourceBody848_227 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_223 sourceBody848_226

def sourceBody848_228 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_222 sourceBody848_227

def sourceBody848_229 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_221 sourceBody848_228

def sourceBody848_230 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_220 sourceBody848_229

def sourceBody848_231 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_0 sourceBody848_230

def sourceBody848_232 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_0 sourceBody848_231

def sourceBody848_233 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_219 sourceBody848_232

def sourceBody848_234 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody848_0, 848, 30)) (some 68) ([2]) (some (2, sourceBody848_100, 848, 31))

def sourceBody848_235 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_234 sourceBody848_4

def sourceBody848_236 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_235 sourceBody848_0

def sourceBody848_237 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_99 sourceBody848_236

def sourceBody848_238 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
        [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
          Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
            (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
      Flapjack.WordLangExpHOL.const 504#64])

def sourceBody848_239 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_238 sourceBody848_113

def sourceBody848_240 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_0 sourceBody848_239

def sourceBody848_241 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_237 sourceBody848_240

def sourceBody848_242 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_0 sourceBody848_241

def sourceBody848_243 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_0 sourceBody848_242

def sourceBody848_244 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_233 sourceBody848_243

def sourceBody848_245 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 504#64]))

def sourceBody848_246 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 25814#64)

def sourceBody848_247 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 8669529151676140297#64)

def sourceBody848_248 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 4307224735379260034#64)

def sourceBody848_249 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody848_0, 848, 32)) (some 847) ([2, 8, 6, 12]) (some (2, sourceBody848_100, 848, 33))

def sourceBody848_250 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_249 sourceBody848_4

def sourceBody848_251 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_250 sourceBody848_0

def sourceBody848_252 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_248 sourceBody848_251

def sourceBody848_253 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_247 sourceBody848_252

def sourceBody848_254 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_246 sourceBody848_253

def sourceBody848_255 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_245 sourceBody848_254

def sourceBody848_256 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_0 sourceBody848_255

def sourceBody848_257 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_0 sourceBody848_256

def sourceBody848_258 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_244 sourceBody848_257

def sourceBody848_259 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody848_0, 848, 34)) (some 68) ([2]) (some (2, sourceBody848_100, 848, 35))

def sourceBody848_260 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_259 sourceBody848_4

def sourceBody848_261 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_260 sourceBody848_0

def sourceBody848_262 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_99 sourceBody848_261

def sourceBody848_263 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
        [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
          Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
            (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
      Flapjack.WordLangExpHOL.const 512#64])

def sourceBody848_264 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_263 sourceBody848_113

def sourceBody848_265 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_0 sourceBody848_264

def sourceBody848_266 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_262 sourceBody848_265

def sourceBody848_267 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_0 sourceBody848_266

def sourceBody848_268 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_0 sourceBody848_267

def sourceBody848_269 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_258 sourceBody848_268

def sourceBody848_270 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 512#64]))

def sourceBody848_271 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody848_272 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 2421447037043915651#64)

def sourceBody848_273 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 11294470620239562234#64)

def sourceBody848_274 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody848_0, 848, 36)) (some 847) ([2, 8, 6, 12]) (some (2, sourceBody848_100, 848, 37))

def sourceBody848_275 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_274 sourceBody848_4

def sourceBody848_276 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_275 sourceBody848_0

def sourceBody848_277 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_273 sourceBody848_276

def sourceBody848_278 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_272 sourceBody848_277

def sourceBody848_279 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_271 sourceBody848_278

def sourceBody848_280 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_270 sourceBody848_279

def sourceBody848_281 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_0 sourceBody848_280

def sourceBody848_282 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_0 sourceBody848_281

def sourceBody848_283 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_269 sourceBody848_282

def sourceBody848_284 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody848_0, 848, 38)) (some 68) ([2]) (some (2, sourceBody848_100, 848, 39))

def sourceBody848_285 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_284 sourceBody848_4

def sourceBody848_286 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_285 sourceBody848_0

def sourceBody848_287 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_23 sourceBody848_286

def sourceBody848_288 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
        [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
          Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
            (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
      Flapjack.WordLangExpHOL.const 520#64])

def sourceBody848_289 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_288 sourceBody848_113

def sourceBody848_290 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_0 sourceBody848_289

def sourceBody848_291 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_287 sourceBody848_290

def sourceBody848_292 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_0 sourceBody848_291

def sourceBody848_293 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_0 sourceBody848_292

def sourceBody848_294 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_283 sourceBody848_293

def sourceBody848_295 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 520#64]),
      Flapjack.WordLangExpHOL.const 0#64])

def sourceBody848_296 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 7249595157780304706#64)

def sourceBody848_297 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody848_0, 848, 40)) (some 89) ([2, 8]) (some (2, sourceBody848_100, 848, 41))

def sourceBody848_298 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_297 sourceBody848_4

def sourceBody848_299 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_298 sourceBody848_0

def sourceBody848_300 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_296 sourceBody848_299

def sourceBody848_301 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_295 sourceBody848_300

def sourceBody848_302 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_0 sourceBody848_301

def sourceBody848_303 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_0 sourceBody848_302

def sourceBody848_304 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_294 sourceBody848_303

def sourceBody848_305 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 520#64]),
      Flapjack.WordLangExpHOL.const 8#64])

def sourceBody848_306 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 12676030261858484297#64)

def sourceBody848_307 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody848_0, 848, 42)) (some 89) ([2, 8]) (some (2, sourceBody848_100, 848, 43))

def sourceBody848_308 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_307 sourceBody848_4

def sourceBody848_309 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_308 sourceBody848_0

def sourceBody848_310 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_306 sourceBody848_309

def sourceBody848_311 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_305 sourceBody848_310

def sourceBody848_312 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_0 sourceBody848_311

def sourceBody848_313 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_0 sourceBody848_312

def sourceBody848_314 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_304 sourceBody848_313

def sourceBody848_315 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 520#64]),
      Flapjack.WordLangExpHOL.const 16#64])

def sourceBody848_316 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 16708898399860066458#64)

def sourceBody848_317 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody848_0, 848, 44)) (some 89) ([2, 8]) (some (2, sourceBody848_100, 848, 45))

def sourceBody848_318 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_317 sourceBody848_4

def sourceBody848_319 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_318 sourceBody848_0

def sourceBody848_320 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_316 sourceBody848_319

def sourceBody848_321 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_315 sourceBody848_320

def sourceBody848_322 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_0 sourceBody848_321

def sourceBody848_323 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_0 sourceBody848_322

def sourceBody848_324 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_314 sourceBody848_323

def sourceBody848_325 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 520#64]),
      Flapjack.WordLangExpHOL.const 24#64])

def sourceBody848_326 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 12074291595689605317#64)

def sourceBody848_327 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody848_0, 848, 46)) (some 89) ([2, 8]) (some (2, sourceBody848_100, 848, 47))

def sourceBody848_328 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_327 sourceBody848_4

def sourceBody848_329 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_328 sourceBody848_0

def sourceBody848_330 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_326 sourceBody848_329

def sourceBody848_331 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_325 sourceBody848_330

def sourceBody848_332 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_0 sourceBody848_331

def sourceBody848_333 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_0 sourceBody848_332

def sourceBody848_334 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_324 sourceBody848_333

def sourceBody848_335 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody848_336 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [10]

def sourceBody848_337 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_336 sourceBody848_0

def sourceBody848_338 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_335 sourceBody848_337

def sourceBody848_339 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_334 sourceBody848_338

def sourceBody848_340 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_54 sourceBody848_339

def sourceBody848_341 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_0 sourceBody848_340

def sourceBody848_342 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody848_53 sourceBody848_341

def source848 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (848, 1, sourceBody848_342)
end InitECandidate.Proofs.WordStages
