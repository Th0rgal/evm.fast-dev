import InitECandidate.Proofs.WordStages.Source808
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody824_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody824_1 : WordLangProgHOL (BitVec 64) :=
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

def sourceBody824_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 96#64]))

def sourceBody824_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 14)

def sourceBody824_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 192#64)

def sourceBody824_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody824_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody824_7 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.reg 8) sourceBody824_5 sourceBody824_6

def sourceBody824_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody824_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody824_7 sourceBody824_8

def sourceBody824_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 12)

def sourceBody824_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 13#64)

def sourceBody824_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 4)

def sourceBody824_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody824_12 sourceBody824_0

def sourceBody824_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody824_13 sourceBody824_0

def sourceBody824_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody824_11 sourceBody824_14

def sourceBody824_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody824_0 sourceBody824_15

def sourceBody824_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 8#64)

def sourceBody824_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 4

def sourceBody824_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody824_17 sourceBody824_18

def sourceBody824_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody824_16 sourceBody824_19

def sourceBody824_21 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 16 (Flapjack.WordRegImm.imm 0#64) sourceBody824_20 sourceBody824_0

def sourceBody824_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody824_21 sourceBody824_8

def sourceBody824_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody824_22 sourceBody824_0

def sourceBody824_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody824_10 sourceBody824_23

def sourceBody824_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody824_9 sourceBody824_24

def sourceBody824_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody824_4 sourceBody824_25

def sourceBody824_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody824_3 sourceBody824_26

def sourceBody824_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 50000#64)

def sourceBody824_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody824_30 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody824_0, 824, 2)) (some 466) ([12]) (some (12, sourceBody824_29, 824, 3))

def sourceBody824_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody824_30 sourceBody824_8

def sourceBody824_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody824_31 sourceBody824_0

def sourceBody824_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody824_28 sourceBody824_32

def sourceBody824_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody824_0 sourceBody824_33

def sourceBody824_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody824_0 sourceBody824_34

def sourceBody824_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody824_27 sourceBody824_35

def sourceBody824_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 64#64)

def sourceBody824_38 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody824_0, 824, 4)) (some 68) ([12]) (some (12, sourceBody824_29, 824, 5))

def sourceBody824_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody824_38 sourceBody824_8

def sourceBody824_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody824_39 sourceBody824_0

def sourceBody824_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody824_37 sourceBody824_40

def sourceBody824_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 88#64]))

def sourceBody824_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 4)

def sourceBody824_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody824_45 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody824_0, 824, 6)) (some 813) ([8, 16]) (some (8, sourceBody824_44, 824, 7))

def sourceBody824_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody824_45 sourceBody824_8

def sourceBody824_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody824_46 sourceBody824_0

def sourceBody824_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody824_43 sourceBody824_47

def sourceBody824_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody824_42 sourceBody824_48

def sourceBody824_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody824_51 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody824_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody824_53 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 16 (Flapjack.WordRegImm.reg 2) sourceBody824_51 sourceBody824_52

def sourceBody824_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody824_53 sourceBody824_8

def sourceBody824_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 16)

def sourceBody824_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 13#64)

def sourceBody824_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 8)

def sourceBody824_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody824_57 sourceBody824_0

def sourceBody824_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody824_58 sourceBody824_0

def sourceBody824_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody824_56 sourceBody824_59

def sourceBody824_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody824_0 sourceBody824_60

def sourceBody824_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 8#64)

def sourceBody824_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody824_62 sourceBody824_44

def sourceBody824_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody824_61 sourceBody824_63

def sourceBody824_65 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.imm 0#64) sourceBody824_64 sourceBody824_0

def sourceBody824_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody824_65 sourceBody824_8

def sourceBody824_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody824_66 sourceBody824_0

def sourceBody824_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody824_55 sourceBody824_67

def sourceBody824_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody824_54 sourceBody824_68

def sourceBody824_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody824_50 sourceBody824_69

def sourceBody824_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody824_10 sourceBody824_70

def sourceBody824_72 : WordLangProgHOL (BitVec 64) :=
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

def sourceBody824_73 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 16)

def sourceBody824_74 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 8) 2

def sourceBody824_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody824_74 sourceBody824_0

def sourceBody824_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody824_73 sourceBody824_75

def sourceBody824_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody824_76 sourceBody824_0

def sourceBody824_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody824_43 sourceBody824_77

def sourceBody824_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody824_0 sourceBody824_78

def sourceBody824_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody824_72 sourceBody824_79

def sourceBody824_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody824_0 sourceBody824_80

def sourceBody824_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody824_71 sourceBody824_81

def sourceBody824_83 : WordLangProgHOL (BitVec 64) :=
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

def sourceBody824_84 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 64#64)

def sourceBody824_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody824_84 sourceBody824_77

def sourceBody824_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody824_0 sourceBody824_85

def sourceBody824_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody824_83 sourceBody824_86

def sourceBody824_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody824_0 sourceBody824_87

def sourceBody824_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody824_82 sourceBody824_88

def sourceBody824_90 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody824_91 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [8]

def sourceBody824_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody824_91 sourceBody824_0

def sourceBody824_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody824_90 sourceBody824_92

def sourceBody824_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody824_89 sourceBody824_93

def sourceBody824_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody824_49 sourceBody824_94

def sourceBody824_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody824_0 sourceBody824_95

def sourceBody824_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody824_0 sourceBody824_96

def sourceBody824_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody824_41 sourceBody824_97

def sourceBody824_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody824_0 sourceBody824_98

def sourceBody824_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody824_0 sourceBody824_99

def sourceBody824_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody824_36 sourceBody824_100

def sourceBody824_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody824_2 sourceBody824_101

def sourceBody824_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody824_0 sourceBody824_102

def sourceBody824_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody824_1 sourceBody824_103

def sourceBody824_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody824_0 sourceBody824_104

def source824 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (824, 1, sourceBody824_105)
end InitECandidate.Proofs.WordStages
