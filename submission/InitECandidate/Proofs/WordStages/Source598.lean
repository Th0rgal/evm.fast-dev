import InitECandidate.Proofs.WordStages.Source582
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody598_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody598_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody598_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody598_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 6)

def sourceBody598_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody598_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody598_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody598_7 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 4 (Flapjack.WordRegImm.reg 10) sourceBody598_5 sourceBody598_6

def sourceBody598_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_7 sourceBody598_2

def sourceBody598_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 4)

def sourceBody598_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody598_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.load
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
            [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                  Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                    (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                    (Flapjack.WordLangExpHOL.const 1#64)],
              Flapjack.WordLangExpHOL.const 288#64]),
        Flapjack.WordLangExpHOL.const 32#64]))

def sourceBody598_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody598_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody598_14 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.reg 8) sourceBody598_13 sourceBody598_4

def sourceBody598_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_14 sourceBody598_2

def sourceBody598_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 10)

def sourceBody598_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody598_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_17 sourceBody598_0

def sourceBody598_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_18 sourceBody598_0

def sourceBody598_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
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
        Flapjack.WordLangExpHOL.const 104#64]))

def sourceBody598_21 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 10 (Flapjack.WordRegImm.reg 8) sourceBody598_13 sourceBody598_4

def sourceBody598_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_21 sourceBody598_2

def sourceBody598_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
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
        Flapjack.WordLangExpHOL.const 0#64]))

def sourceBody598_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
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
        Flapjack.WordLangExpHOL.const 56#64]))

def sourceBody598_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody598_26 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notLower) 8 (Flapjack.WordRegImm.reg 14) sourceBody598_25 sourceBody598_12

def sourceBody598_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_26 sourceBody598_2

def sourceBody598_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 8)

def sourceBody598_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
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
            Flapjack.WordLangExpHOL.const 48#64]),
      Flapjack.WordLangExpHOL.var 4])

def sourceBody598_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 14 (Flapjack.WordLangAddr.addr 14 0#64))

def sourceBody598_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 14)

def sourceBody598_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody598_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.lookup (Flapjack.WordStore.temp 0#5))

def sourceBody598_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_33 sourceBody598_0

def sourceBody598_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_34 sourceBody598_0

def sourceBody598_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 10)

def sourceBody598_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 2

def sourceBody598_38 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody598_0, 598, 3)) (some 593) ([2]) (some (2, sourceBody598_37, 598, 4))

def sourceBody598_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_38 sourceBody598_2

def sourceBody598_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_39 sourceBody598_0

def sourceBody598_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_36 sourceBody598_40

def sourceBody598_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_0 sourceBody598_41

def sourceBody598_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_0 sourceBody598_42

def sourceBody598_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_35 sourceBody598_43

def sourceBody598_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_2 sourceBody598_44

def sourceBody598_46 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.WordRegImm.imm 8#64) sourceBody598_32 sourceBody598_45

def sourceBody598_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_46 sourceBody598_2

def sourceBody598_48 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody598_0, 598, 2)) (some 591) ([2]) (some (14, sourceBody598_47, 598, 5))

def sourceBody598_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_48 sourceBody598_2

def sourceBody598_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_49 sourceBody598_0

def sourceBody598_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_31 sourceBody598_50

def sourceBody598_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_30 sourceBody598_51

def sourceBody598_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_29 sourceBody598_52

def sourceBody598_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_0 sourceBody598_53

def sourceBody598_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_0 sourceBody598_54

def sourceBody598_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_0 sourceBody598_55

def sourceBody598_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_0 sourceBody598_56

def sourceBody598_58 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 2 (Flapjack.WordRegImm.imm 0#64) sourceBody598_19 sourceBody598_57

def sourceBody598_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_58 sourceBody598_2

def sourceBody598_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_59 sourceBody598_0

def sourceBody598_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_28 sourceBody598_60

def sourceBody598_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_27 sourceBody598_61

def sourceBody598_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_24 sourceBody598_62

def sourceBody598_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_9 sourceBody598_63

def sourceBody598_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_23 sourceBody598_64

def sourceBody598_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_0 sourceBody598_65

def sourceBody598_67 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.WordRegImm.imm 0#64) sourceBody598_19 sourceBody598_66

def sourceBody598_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_67 sourceBody598_2

def sourceBody598_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_68 sourceBody598_0

def sourceBody598_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_16 sourceBody598_69

def sourceBody598_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_22 sourceBody598_70

def sourceBody598_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_12 sourceBody598_71

def sourceBody598_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_20 sourceBody598_72

def sourceBody598_74 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.WordRegImm.imm 0#64) sourceBody598_19 sourceBody598_73

def sourceBody598_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_74 sourceBody598_2

def sourceBody598_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_75 sourceBody598_0

def sourceBody598_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_16 sourceBody598_76

def sourceBody598_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_15 sourceBody598_77

def sourceBody598_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_12 sourceBody598_78

def sourceBody598_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_11 sourceBody598_79

def sourceBody598_81 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 12)

def sourceBody598_82 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody598_83 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody598_0, 598, 6)) (some 596) ([]) (some (10, sourceBody598_82, 598, 7))

def sourceBody598_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_83 sourceBody598_2

def sourceBody598_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_84 sourceBody598_0

def sourceBody598_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_0 sourceBody598_85

def sourceBody598_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_0 sourceBody598_86

def sourceBody598_88 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.load
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
            [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                  Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                    (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                    (Flapjack.WordLangExpHOL.const 1#64)],
              Flapjack.WordLangExpHOL.const 288#64]),
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody598_89 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
        [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
          Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
            (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
      Flapjack.WordLangExpHOL.const 256#64])

def sourceBody598_90 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.load
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
            [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                  Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                    (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                    (Flapjack.WordLangExpHOL.const 1#64)],
              Flapjack.WordLangExpHOL.const 288#64]),
        Flapjack.WordLangExpHOL.const 0#64]))

def sourceBody598_91 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 10)

def sourceBody598_92 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 4) 8

def sourceBody598_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_92 sourceBody598_0

def sourceBody598_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_91 sourceBody598_93

def sourceBody598_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_94 sourceBody598_0

def sourceBody598_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_90 sourceBody598_95

def sourceBody598_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_0 sourceBody598_96

def sourceBody598_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_89 sourceBody598_97

def sourceBody598_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_0 sourceBody598_98

def sourceBody598_100 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
        [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
          Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
            (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
      Flapjack.WordLangExpHOL.const 288#64])

def sourceBody598_101 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.load
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
            [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                  Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                    (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                    (Flapjack.WordLangExpHOL.const 1#64)],
              Flapjack.WordLangExpHOL.const 288#64]),
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody598_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_101 sourceBody598_95

def sourceBody598_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_0 sourceBody598_102

def sourceBody598_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_100 sourceBody598_103

def sourceBody598_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_0 sourceBody598_104

def sourceBody598_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_99 sourceBody598_105

def sourceBody598_107 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody598_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_107 sourceBody598_0

def sourceBody598_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_108 sourceBody598_0

def sourceBody598_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_106 sourceBody598_109

def sourceBody598_111 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody598_112 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.lookup (Flapjack.WordStore.temp 0#5))

def sourceBody598_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_112 sourceBody598_0

def sourceBody598_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_113 sourceBody598_0

def sourceBody598_115 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 4)

def sourceBody598_116 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody598_0, 598, 9)) (some 593) ([14]) (some (14, sourceBody598_32, 598, 10))

def sourceBody598_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_116 sourceBody598_2

def sourceBody598_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_117 sourceBody598_0

def sourceBody598_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_115 sourceBody598_118

def sourceBody598_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_0 sourceBody598_119

def sourceBody598_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_0 sourceBody598_120

def sourceBody598_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_114 sourceBody598_121

def sourceBody598_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_2 sourceBody598_122

def sourceBody598_124 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.WordRegImm.imm 8#64) sourceBody598_111 sourceBody598_123

def sourceBody598_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_124 sourceBody598_2

def sourceBody598_126 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody598_0, 598, 8)) (some 597) ([]) (some (8, sourceBody598_125, 598, 11))

def sourceBody598_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_126 sourceBody598_2

def sourceBody598_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_127 sourceBody598_0

def sourceBody598_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_0 sourceBody598_128

def sourceBody598_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_0 sourceBody598_129

def sourceBody598_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_0 sourceBody598_130

def sourceBody598_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_0 sourceBody598_131

def sourceBody598_133 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.WordRegImm.imm 0#64) sourceBody598_110 sourceBody598_132

def sourceBody598_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_133 sourceBody598_2

def sourceBody598_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_134 sourceBody598_0

def sourceBody598_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_16 sourceBody598_135

def sourceBody598_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_22 sourceBody598_136

def sourceBody598_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_12 sourceBody598_137

def sourceBody598_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_88 sourceBody598_138

def sourceBody598_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_87 sourceBody598_139

def sourceBody598_141 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.WordRegImm.imm 0#64) sourceBody598_140 sourceBody598_0

def sourceBody598_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_141 sourceBody598_2

def sourceBody598_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_142 sourceBody598_0

def sourceBody598_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_16 sourceBody598_143

def sourceBody598_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_15 sourceBody598_144

def sourceBody598_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_12 sourceBody598_145

def sourceBody598_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_81 sourceBody598_146

def sourceBody598_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_80 sourceBody598_147

def sourceBody598_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_10 sourceBody598_148

def sourceBody598_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_0 sourceBody598_149

def sourceBody598_151 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody598_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_150 sourceBody598_151

def sourceBody598_153 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody598_154 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.WordRegImm.imm 0#64) sourceBody598_152 sourceBody598_153

def sourceBody598_155 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_154 sourceBody598_2

def sourceBody598_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_155 sourceBody598_0

def sourceBody598_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_9 sourceBody598_156

def sourceBody598_158 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_8 sourceBody598_157

def sourceBody598_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_4 sourceBody598_158

def sourceBody598_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_3 sourceBody598_159

def sourceBody598_161 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln) sourceBody598_160 (Flapjack.Spt.ls PUnit.unit)

def sourceBody598_162 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_161 sourceBody598_2

def sourceBody598_163 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_2 sourceBody598_162

def sourceBody598_164 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [12]

def sourceBody598_165 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_164 sourceBody598_0

def sourceBody598_166 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_10 sourceBody598_165

def sourceBody598_167 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_163 sourceBody598_166

def sourceBody598_168 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_1 sourceBody598_167

def sourceBody598_169 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody598_0 sourceBody598_168

def source598 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (598, 1, sourceBody598_169)
end InitECandidate.Proofs.WordStages
