import InitECandidate.Proofs.WordStages.Source806
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody822_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody822_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
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
        Flapjack.WordLangExpHOL.const 112#64]))

def sourceBody822_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 96#64]))

def sourceBody822_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 14)

def sourceBody822_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 64#64)

def sourceBody822_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody822_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody822_7 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.reg 8) sourceBody822_5 sourceBody822_6

def sourceBody822_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody822_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody822_7 sourceBody822_8

def sourceBody822_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 12)

def sourceBody822_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 10#64)

def sourceBody822_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 4)

def sourceBody822_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody822_12 sourceBody822_0

def sourceBody822_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody822_13 sourceBody822_0

def sourceBody822_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody822_11 sourceBody822_14

def sourceBody822_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody822_0 sourceBody822_15

def sourceBody822_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 8#64)

def sourceBody822_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 4

def sourceBody822_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody822_17 sourceBody822_18

def sourceBody822_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody822_16 sourceBody822_19

def sourceBody822_21 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 16 (Flapjack.WordRegImm.imm 0#64) sourceBody822_20 sourceBody822_0

def sourceBody822_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody822_21 sourceBody822_8

def sourceBody822_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody822_22 sourceBody822_0

def sourceBody822_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody822_10 sourceBody822_23

def sourceBody822_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody822_9 sourceBody822_24

def sourceBody822_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody822_4 sourceBody822_25

def sourceBody822_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody822_3 sourceBody822_26

def sourceBody822_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 5500#64)

def sourceBody822_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody822_30 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody822_0, 822, 2)) (some 466) ([12]) (some (12, sourceBody822_29, 822, 3))

def sourceBody822_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody822_30 sourceBody822_8

def sourceBody822_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody822_31 sourceBody822_0

def sourceBody822_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody822_28 sourceBody822_32

def sourceBody822_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody822_0 sourceBody822_33

def sourceBody822_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody822_0 sourceBody822_34

def sourceBody822_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody822_27 sourceBody822_35

def sourceBody822_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 128#64)

def sourceBody822_38 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody822_0, 822, 4)) (some 68) ([12]) (some (12, sourceBody822_29, 822, 5))

def sourceBody822_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody822_38 sourceBody822_8

def sourceBody822_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody822_39 sourceBody822_0

def sourceBody822_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody822_37 sourceBody822_40

def sourceBody822_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 88#64]))

def sourceBody822_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 4)

def sourceBody822_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody822_45 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody822_0, 822, 6)) (some 811) ([8, 16]) (some (8, sourceBody822_44, 822, 7))

def sourceBody822_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody822_45 sourceBody822_8

def sourceBody822_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody822_46 sourceBody822_0

def sourceBody822_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody822_43 sourceBody822_47

def sourceBody822_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody822_42 sourceBody822_48

def sourceBody822_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody822_51 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody822_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody822_53 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 16 (Flapjack.WordRegImm.reg 2) sourceBody822_51 sourceBody822_52

def sourceBody822_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody822_53 sourceBody822_8

def sourceBody822_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 16)

def sourceBody822_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 10#64)

def sourceBody822_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 8)

def sourceBody822_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody822_57 sourceBody822_0

def sourceBody822_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody822_58 sourceBody822_0

def sourceBody822_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody822_56 sourceBody822_59

def sourceBody822_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody822_0 sourceBody822_60

def sourceBody822_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 8#64)

def sourceBody822_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody822_62 sourceBody822_44

def sourceBody822_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody822_61 sourceBody822_63

def sourceBody822_65 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.imm 0#64) sourceBody822_64 sourceBody822_0

def sourceBody822_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody822_65 sourceBody822_8

def sourceBody822_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody822_66 sourceBody822_0

def sourceBody822_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody822_55 sourceBody822_67

def sourceBody822_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody822_54 sourceBody822_68

def sourceBody822_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody822_50 sourceBody822_69

def sourceBody822_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody822_10 sourceBody822_70

def sourceBody822_72 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 256#64]),
      Flapjack.WordLangExpHOL.const 120#64])

def sourceBody822_73 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 16)

def sourceBody822_74 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 8) 2

def sourceBody822_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody822_74 sourceBody822_0

def sourceBody822_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody822_73 sourceBody822_75

def sourceBody822_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody822_76 sourceBody822_0

def sourceBody822_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody822_43 sourceBody822_77

def sourceBody822_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody822_0 sourceBody822_78

def sourceBody822_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody822_72 sourceBody822_79

def sourceBody822_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody822_0 sourceBody822_80

def sourceBody822_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody822_71 sourceBody822_81

def sourceBody822_83 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 256#64]),
      Flapjack.WordLangExpHOL.const 128#64])

def sourceBody822_84 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 128#64)

def sourceBody822_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody822_84 sourceBody822_77

def sourceBody822_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody822_0 sourceBody822_85

def sourceBody822_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody822_83 sourceBody822_86

def sourceBody822_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody822_0 sourceBody822_87

def sourceBody822_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody822_82 sourceBody822_88

def sourceBody822_90 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody822_91 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [8]

def sourceBody822_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody822_91 sourceBody822_0

def sourceBody822_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody822_90 sourceBody822_92

def sourceBody822_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody822_89 sourceBody822_93

def sourceBody822_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody822_49 sourceBody822_94

def sourceBody822_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody822_0 sourceBody822_95

def sourceBody822_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody822_0 sourceBody822_96

def sourceBody822_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody822_41 sourceBody822_97

def sourceBody822_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody822_0 sourceBody822_98

def sourceBody822_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody822_0 sourceBody822_99

def sourceBody822_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody822_36 sourceBody822_100

def sourceBody822_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody822_2 sourceBody822_101

def sourceBody822_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody822_0 sourceBody822_102

def sourceBody822_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody822_1 sourceBody822_103

def sourceBody822_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody822_0 sourceBody822_104

def source822 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (822, 1, sourceBody822_105)
end InitECandidate.Proofs.WordStages
