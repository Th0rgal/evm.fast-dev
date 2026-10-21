import InitECandidate.Proofs.WordStages.Source451
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody467_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody467_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
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
        Flapjack.WordLangExpHOL.const 72#64]))

def sourceBody467_2 : WordLangProgHOL (BitVec 64) :=
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
        Flapjack.WordLangExpHOL.const 64#64]))

def sourceBody467_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 8)

def sourceBody467_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 2)

def sourceBody467_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody467_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody467_7 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notLower) 12 (Flapjack.WordRegImm.reg 10) sourceBody467_5 sourceBody467_6

def sourceBody467_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody467_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody467_7 sourceBody467_8

def sourceBody467_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 12)

def sourceBody467_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 256#64]),
      Flapjack.WordLangExpHOL.const 72#64])

def sourceBody467_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.var 2])

def sourceBody467_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 12)

def sourceBody467_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 6) 10

def sourceBody467_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody467_14 sourceBody467_0

def sourceBody467_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody467_13 sourceBody467_15

def sourceBody467_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody467_16 sourceBody467_0

def sourceBody467_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody467_12 sourceBody467_17

def sourceBody467_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody467_0 sourceBody467_18

def sourceBody467_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody467_11 sourceBody467_19

def sourceBody467_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody467_0 sourceBody467_20

def sourceBody467_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody467_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [6]

def sourceBody467_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody467_23 sourceBody467_0

def sourceBody467_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody467_22 sourceBody467_24

def sourceBody467_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody467_21 sourceBody467_25

def sourceBody467_27 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 16 (Flapjack.WordRegImm.imm 0#64) sourceBody467_26 sourceBody467_0

def sourceBody467_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody467_27 sourceBody467_8

def sourceBody467_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody467_28 sourceBody467_0

def sourceBody467_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody467_10 sourceBody467_29

def sourceBody467_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody467_9 sourceBody467_30

def sourceBody467_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody467_4 sourceBody467_31

def sourceBody467_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody467_3 sourceBody467_32

def sourceBody467_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 14)

def sourceBody467_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody467_36 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody467_0, 467, 2)) (some 459) ([12, 10]) (some (12, sourceBody467_35, 467, 3))

def sourceBody467_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody467_36 sourceBody467_8

def sourceBody467_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody467_37 sourceBody467_0

def sourceBody467_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody467_34 sourceBody467_38

def sourceBody467_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody467_3 sourceBody467_39

def sourceBody467_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 6)

def sourceBody467_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 2)

def sourceBody467_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody467_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody467_45 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notLower) 10 (Flapjack.WordRegImm.reg 16) sourceBody467_43 sourceBody467_44

def sourceBody467_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody467_45 sourceBody467_8

def sourceBody467_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 10)

def sourceBody467_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.var 8])

def sourceBody467_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 256#64]),
      Flapjack.WordLangExpHOL.const 72#64])

def sourceBody467_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody467_51 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 16)

def sourceBody467_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 10) 4

def sourceBody467_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody467_52 sourceBody467_0

def sourceBody467_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody467_51 sourceBody467_53

def sourceBody467_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody467_54 sourceBody467_0

def sourceBody467_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody467_50 sourceBody467_55

def sourceBody467_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody467_0 sourceBody467_56

def sourceBody467_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody467_49 sourceBody467_57

def sourceBody467_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody467_0 sourceBody467_58

def sourceBody467_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 256#64]),
      Flapjack.WordLangExpHOL.const 64#64])

def sourceBody467_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.var 12])

def sourceBody467_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody467_61 sourceBody467_55

def sourceBody467_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody467_0 sourceBody467_62

def sourceBody467_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody467_60 sourceBody467_63

def sourceBody467_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody467_0 sourceBody467_64

def sourceBody467_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody467_59 sourceBody467_65

def sourceBody467_67 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 256#64]),
      Flapjack.WordLangExpHOL.const 192#64])

def sourceBody467_68 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
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
            Flapjack.WordLangExpHOL.const 192#64]),
      Flapjack.WordLangExpHOL.var 12])

def sourceBody467_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody467_68 sourceBody467_55

def sourceBody467_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody467_0 sourceBody467_69

def sourceBody467_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody467_67 sourceBody467_70

def sourceBody467_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody467_0 sourceBody467_71

def sourceBody467_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody467_66 sourceBody467_72

def sourceBody467_74 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [10]

def sourceBody467_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody467_74 sourceBody467_0

def sourceBody467_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody467_44 sourceBody467_75

def sourceBody467_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody467_73 sourceBody467_76

def sourceBody467_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody467_48 sourceBody467_77

def sourceBody467_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody467_0 sourceBody467_78

def sourceBody467_80 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 4 (Flapjack.WordRegImm.imm 0#64) sourceBody467_79 sourceBody467_0

def sourceBody467_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody467_80 sourceBody467_8

def sourceBody467_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody467_81 sourceBody467_0

def sourceBody467_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody467_47 sourceBody467_82

def sourceBody467_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody467_46 sourceBody467_83

def sourceBody467_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody467_42 sourceBody467_84

def sourceBody467_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody467_41 sourceBody467_85

def sourceBody467_87 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 4#64)

def sourceBody467_88 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 12)

def sourceBody467_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody467_88 sourceBody467_0

def sourceBody467_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody467_89 sourceBody467_0

def sourceBody467_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody467_87 sourceBody467_90

def sourceBody467_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody467_0 sourceBody467_91

def sourceBody467_93 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 8#64)

def sourceBody467_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody467_93 sourceBody467_35

def sourceBody467_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody467_92 sourceBody467_94

def sourceBody467_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody467_86 sourceBody467_95

def sourceBody467_97 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [12]

def sourceBody467_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody467_97 sourceBody467_0

def sourceBody467_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody467_6 sourceBody467_98

def sourceBody467_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody467_96 sourceBody467_99

def sourceBody467_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody467_40 sourceBody467_100

def sourceBody467_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody467_0 sourceBody467_101

def sourceBody467_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody467_0 sourceBody467_102

def sourceBody467_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody467_33 sourceBody467_103

def sourceBody467_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody467_2 sourceBody467_104

def sourceBody467_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody467_0 sourceBody467_105

def sourceBody467_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody467_1 sourceBody467_106

def sourceBody467_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody467_0 sourceBody467_107

def source467 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (467, 2, sourceBody467_108)
end InitECandidate.Proofs.WordStages
