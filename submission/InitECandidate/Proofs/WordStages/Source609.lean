import InitECandidate.Proofs.WordStages.Source593
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody609_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 4)

def sourceBody609_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody609_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody609_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody609_4 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 8 (Flapjack.WordRegImm.reg 12) sourceBody609_2 sourceBody609_3

def sourceBody609_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody609_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody609_4 sourceBody609_5

def sourceBody609_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 8)

def sourceBody609_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody609_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 256#64]),
      Flapjack.WordLangExpHOL.const 144#64])

def sourceBody609_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 264#64]))

def sourceBody609_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 8)

def sourceBody609_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 14) 12

def sourceBody609_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody609_12 sourceBody609_8

def sourceBody609_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody609_11 sourceBody609_13

def sourceBody609_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody609_14 sourceBody609_8

def sourceBody609_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody609_10 sourceBody609_15

def sourceBody609_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody609_8 sourceBody609_16

def sourceBody609_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody609_9 sourceBody609_17

def sourceBody609_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody609_8 sourceBody609_18

def sourceBody609_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 256#64]),
      Flapjack.WordLangExpHOL.const 152#64])

def sourceBody609_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody609_3 sourceBody609_15

def sourceBody609_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody609_8 sourceBody609_21

def sourceBody609_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody609_20 sourceBody609_22

def sourceBody609_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody609_8 sourceBody609_23

def sourceBody609_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody609_19 sourceBody609_24

def sourceBody609_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 256#64]),
      Flapjack.WordLangExpHOL.const 216#64])

def sourceBody609_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody609_26 sourceBody609_22

def sourceBody609_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody609_8 sourceBody609_27

def sourceBody609_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody609_25 sourceBody609_28

def sourceBody609_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody609_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [14]

def sourceBody609_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody609_31 sourceBody609_8

def sourceBody609_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody609_30 sourceBody609_32

def sourceBody609_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody609_29 sourceBody609_33

def sourceBody609_35 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.imm 0#64) sourceBody609_34 sourceBody609_8

def sourceBody609_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody609_35 sourceBody609_5

def sourceBody609_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody609_36 sourceBody609_8

def sourceBody609_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody609_7 sourceBody609_37

def sourceBody609_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody609_6 sourceBody609_38

def sourceBody609_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody609_1 sourceBody609_39

def sourceBody609_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody609_0 sourceBody609_40

def sourceBody609_42 : WordLangProgHOL (BitVec 64) :=
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
        Flapjack.WordLangExpHOL.const 216#64]))

def sourceBody609_43 : WordLangProgHOL (BitVec 64) :=
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
        Flapjack.WordLangExpHOL.const 144#64]))

def sourceBody609_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 14)

def sourceBody609_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 4)

def sourceBody609_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody609_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody609_48 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 10 (Flapjack.WordRegImm.reg 16) sourceBody609_46 sourceBody609_47

def sourceBody609_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody609_48 sourceBody609_5

def sourceBody609_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 10)

def sourceBody609_51 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 8#64])

def sourceBody609_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody609_53 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody609_8, 609, 2)) (some 68) ([12]) (some (12, sourceBody609_52, 609, 3))

def sourceBody609_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody609_53 sourceBody609_5

def sourceBody609_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody609_54 sourceBody609_8

def sourceBody609_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody609_51 sourceBody609_55

def sourceBody609_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 256#64]),
      Flapjack.WordLangExpHOL.const 144#64])

def sourceBody609_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 10)

def sourceBody609_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 12) 16

def sourceBody609_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody609_59 sourceBody609_8

def sourceBody609_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody609_58 sourceBody609_60

def sourceBody609_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody609_61 sourceBody609_8

def sourceBody609_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody609_7 sourceBody609_62

def sourceBody609_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody609_8 sourceBody609_63

def sourceBody609_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody609_57 sourceBody609_64

def sourceBody609_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody609_8 sourceBody609_65

def sourceBody609_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody609_56 sourceBody609_66

def sourceBody609_68 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 256#64]),
      Flapjack.WordLangExpHOL.const 216#64])

def sourceBody609_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 4)

def sourceBody609_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody609_69 sourceBody609_62

def sourceBody609_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody609_8 sourceBody609_70

def sourceBody609_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody609_68 sourceBody609_71

def sourceBody609_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody609_8 sourceBody609_72

def sourceBody609_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody609_67 sourceBody609_73

def sourceBody609_75 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.WordRegImm.imm 0#64) sourceBody609_74 sourceBody609_8

def sourceBody609_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody609_75 sourceBody609_5

def sourceBody609_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody609_76 sourceBody609_8

def sourceBody609_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody609_50 sourceBody609_77

def sourceBody609_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody609_49 sourceBody609_78

def sourceBody609_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody609_45 sourceBody609_79

def sourceBody609_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody609_44 sourceBody609_80

def sourceBody609_82 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 2)

def sourceBody609_83 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 4)

def sourceBody609_84 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody609_85 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody609_8, 609, 4)) (some 77) ([10, 16, 6]) (some (10, sourceBody609_84, 609, 5))

def sourceBody609_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody609_85 sourceBody609_5

def sourceBody609_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody609_86 sourceBody609_8

def sourceBody609_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody609_83 sourceBody609_87

def sourceBody609_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody609_82 sourceBody609_88

def sourceBody609_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody609_7 sourceBody609_89

def sourceBody609_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody609_8 sourceBody609_90

def sourceBody609_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody609_8 sourceBody609_91

def sourceBody609_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody609_81 sourceBody609_92

def sourceBody609_94 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 256#64]),
      Flapjack.WordLangExpHOL.const 152#64])

def sourceBody609_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody609_94 sourceBody609_71

def sourceBody609_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody609_8 sourceBody609_95

def sourceBody609_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody609_93 sourceBody609_96

def sourceBody609_98 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [12]

def sourceBody609_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody609_98 sourceBody609_8

def sourceBody609_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody609_1 sourceBody609_99

def sourceBody609_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody609_97 sourceBody609_100

def sourceBody609_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody609_43 sourceBody609_101

def sourceBody609_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody609_8 sourceBody609_102

def sourceBody609_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody609_42 sourceBody609_103

def sourceBody609_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody609_8 sourceBody609_104

def sourceBody609_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody609_41 sourceBody609_105

def source609 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (609, 3, sourceBody609_106)
end InitECandidate.Proofs.WordStages
