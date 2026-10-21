import InitECandidate.Proofs.WordStages.Source456
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody472_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody472_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.load
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
            [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                  Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                    (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                    (Flapjack.WordLangExpHOL.const 1#64)],
              Flapjack.WordLangExpHOL.const 256#64]),
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody472_2 : WordLangProgHOL (BitVec 64) :=
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
              Flapjack.WordLangExpHOL.const 256#64]),
        Flapjack.WordLangExpHOL.const 232#64]))

def sourceBody472_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 20)

def sourceBody472_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 16)

def sourceBody472_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody472_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody472_7 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notLower) 10 (Flapjack.WordRegImm.reg 18) sourceBody472_5 sourceBody472_6

def sourceBody472_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody472_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_7 sourceBody472_8

def sourceBody472_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 10)

def sourceBody472_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 16)

def sourceBody472_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 1024#64)

def sourceBody472_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 3#64)

def sourceBody472_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 24)

def sourceBody472_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_14 sourceBody472_0

def sourceBody472_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_15 sourceBody472_0

def sourceBody472_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_13 sourceBody472_16

def sourceBody472_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_0 sourceBody472_17

def sourceBody472_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 8#64)

def sourceBody472_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 24

def sourceBody472_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_19 sourceBody472_20

def sourceBody472_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_18 sourceBody472_21

def sourceBody472_23 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.WordRegImm.imm 0#64) sourceBody472_22 sourceBody472_0

def sourceBody472_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_23 sourceBody472_8

def sourceBody472_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_24 sourceBody472_0

def sourceBody472_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_10 sourceBody472_25

def sourceBody472_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_9 sourceBody472_26

def sourceBody472_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_12 sourceBody472_27

def sourceBody472_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_11 sourceBody472_28

def sourceBody472_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 16)
    (Flapjack.WordLangExpHOL.const 1#64))

def sourceBody472_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 24)

def sourceBody472_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody472_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody472_34 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 18 (Flapjack.WordRegImm.reg 14) sourceBody472_32 sourceBody472_33

def sourceBody472_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_34 sourceBody472_8

def sourceBody472_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 18)

def sourceBody472_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 1024#64)

def sourceBody472_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_37 sourceBody472_0

def sourceBody472_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_38 sourceBody472_0

def sourceBody472_40 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 22 (Flapjack.WordRegImm.imm 0#64) sourceBody472_39 sourceBody472_0

def sourceBody472_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_40 sourceBody472_8

def sourceBody472_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_41 sourceBody472_0

def sourceBody472_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_36 sourceBody472_42

def sourceBody472_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_35 sourceBody472_43

def sourceBody472_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_31 sourceBody472_44

def sourceBody472_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_12 sourceBody472_45

def sourceBody472_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 24)
    (Flapjack.WordLangExpHOL.const 5#64))

def sourceBody472_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody472_49 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody472_0, 472, 2)) (some 74) ([18]) (some (18, sourceBody472_48, 472, 3))

def sourceBody472_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_49 sourceBody472_8

def sourceBody472_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_50 sourceBody472_0

def sourceBody472_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_47 sourceBody472_51

def sourceBody472_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.load
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
            [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                  Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                    (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                    (Flapjack.WordLangExpHOL.const 1#64)],
              Flapjack.WordLangExpHOL.const 256#64]),
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody472_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 20)
    (Flapjack.WordLangExpHOL.const 5#64))

def sourceBody472_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody472_56 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody472_0, 472, 4)) (some 77) ([14, 22, 12]) (some (14, sourceBody472_55, 472, 5))

def sourceBody472_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_56 sourceBody472_8

def sourceBody472_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_57 sourceBody472_0

def sourceBody472_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_54 sourceBody472_58

def sourceBody472_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_53 sourceBody472_59

def sourceBody472_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_10 sourceBody472_60

def sourceBody472_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_0 sourceBody472_61

def sourceBody472_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_0 sourceBody472_62

def sourceBody472_64 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 256#64]),
      Flapjack.WordLangExpHOL.const 8#64])

def sourceBody472_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 14)

def sourceBody472_66 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 18) 22

def sourceBody472_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_66 sourceBody472_0

def sourceBody472_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_65 sourceBody472_67

def sourceBody472_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_68 sourceBody472_0

def sourceBody472_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_10 sourceBody472_69

def sourceBody472_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_0 sourceBody472_70

def sourceBody472_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_64 sourceBody472_71

def sourceBody472_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_0 sourceBody472_72

def sourceBody472_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_63 sourceBody472_73

def sourceBody472_75 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 256#64]),
      Flapjack.WordLangExpHOL.const 232#64])

def sourceBody472_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_31 sourceBody472_69

def sourceBody472_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_0 sourceBody472_76

def sourceBody472_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_75 sourceBody472_77

def sourceBody472_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_0 sourceBody472_78

def sourceBody472_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_74 sourceBody472_79

def sourceBody472_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_52 sourceBody472_80

def sourceBody472_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_0 sourceBody472_81

def sourceBody472_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_0 sourceBody472_82

def sourceBody472_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_46 sourceBody472_83

def sourceBody472_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_30 sourceBody472_84

def sourceBody472_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_0 sourceBody472_85

def sourceBody472_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_29 sourceBody472_86

def sourceBody472_88 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.WordRegImm.imm 0#64) sourceBody472_87 sourceBody472_0

def sourceBody472_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_88 sourceBody472_8

def sourceBody472_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_89 sourceBody472_0

def sourceBody472_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_10 sourceBody472_90

def sourceBody472_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_9 sourceBody472_91

def sourceBody472_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_4 sourceBody472_92

def sourceBody472_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_3 sourceBody472_93

def sourceBody472_95 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 10 (Flapjack.WordRegImm.reg 18) sourceBody472_5 sourceBody472_6

def sourceBody472_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_95 sourceBody472_8

def sourceBody472_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_96 sourceBody472_26

def sourceBody472_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_12 sourceBody472_97

def sourceBody472_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_3 sourceBody472_98

def sourceBody472_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_94 sourceBody472_99

def sourceBody472_101 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.load
              (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
                [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                    [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                        (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                        (Flapjack.WordLangExpHOL.const 1#64)],
                  Flapjack.WordLangExpHOL.const 256#64]),
            Flapjack.WordLangExpHOL.const 8#64]),
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 20)
        (Flapjack.WordLangExpHOL.const 5#64)])

def sourceBody472_102 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 2)

def sourceBody472_103 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 4)

def sourceBody472_104 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 6)

def sourceBody472_105 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 8)

def sourceBody472_106 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 10)

def sourceBody472_107 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 24) 12

def sourceBody472_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_107 sourceBody472_0

def sourceBody472_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_106 sourceBody472_108

def sourceBody472_110 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 18)

def sourceBody472_111 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 24, Flapjack.WordLangExpHOL.const 8#64])
  12

def sourceBody472_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_111 sourceBody472_0

def sourceBody472_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_110 sourceBody472_112

def sourceBody472_114 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 14)

def sourceBody472_115 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 24, Flapjack.WordLangExpHOL.const 16#64])
  12

def sourceBody472_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_115 sourceBody472_0

def sourceBody472_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_114 sourceBody472_116

def sourceBody472_118 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 22)

def sourceBody472_119 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 24, Flapjack.WordLangExpHOL.const 24#64])
  12

def sourceBody472_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_119 sourceBody472_0

def sourceBody472_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_118 sourceBody472_120

def sourceBody472_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_121 sourceBody472_0

def sourceBody472_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_117 sourceBody472_122

def sourceBody472_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_113 sourceBody472_123

def sourceBody472_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_109 sourceBody472_124

def sourceBody472_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_105 sourceBody472_125

def sourceBody472_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_0 sourceBody472_126

def sourceBody472_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_104 sourceBody472_127

def sourceBody472_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_0 sourceBody472_128

def sourceBody472_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_103 sourceBody472_129

def sourceBody472_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_0 sourceBody472_130

def sourceBody472_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_102 sourceBody472_131

def sourceBody472_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_0 sourceBody472_132

def sourceBody472_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_101 sourceBody472_133

def sourceBody472_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_0 sourceBody472_134

def sourceBody472_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_100 sourceBody472_135

def sourceBody472_137 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 256#64]),
      Flapjack.WordLangExpHOL.const 16#64])

def sourceBody472_138 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 20, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody472_139 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 10)

def sourceBody472_140 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 24) 18

def sourceBody472_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_140 sourceBody472_0

def sourceBody472_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_139 sourceBody472_141

def sourceBody472_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_142 sourceBody472_0

def sourceBody472_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_138 sourceBody472_143

def sourceBody472_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_0 sourceBody472_144

def sourceBody472_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_137 sourceBody472_145

def sourceBody472_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_0 sourceBody472_146

def sourceBody472_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_136 sourceBody472_147

def sourceBody472_149 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody472_150 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [24]

def sourceBody472_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_150 sourceBody472_0

def sourceBody472_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_149 sourceBody472_151

def sourceBody472_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_148 sourceBody472_152

def sourceBody472_154 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_2 sourceBody472_153

def sourceBody472_155 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_0 sourceBody472_154

def sourceBody472_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_1 sourceBody472_155

def sourceBody472_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody472_0 sourceBody472_156

def source472 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (472, 5, sourceBody472_157)
end InitECandidate.Proofs.WordStages
