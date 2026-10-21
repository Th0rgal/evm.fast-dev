import InitECandidate.Proofs.WordStages.Source803
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody819_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody819_1 : WordLangProgHOL (BitVec 64) :=
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

def sourceBody819_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 96#64]))

def sourceBody819_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 14)

def sourceBody819_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 512#64)

def sourceBody819_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody819_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody819_7 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.reg 8) sourceBody819_5 sourceBody819_6

def sourceBody819_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody819_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody819_7 sourceBody819_8

def sourceBody819_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 12)

def sourceBody819_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 10#64)

def sourceBody819_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 4)

def sourceBody819_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody819_12 sourceBody819_0

def sourceBody819_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody819_13 sourceBody819_0

def sourceBody819_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody819_11 sourceBody819_14

def sourceBody819_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody819_0 sourceBody819_15

def sourceBody819_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 8#64)

def sourceBody819_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 4

def sourceBody819_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody819_17 sourceBody819_18

def sourceBody819_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody819_16 sourceBody819_19

def sourceBody819_21 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 16 (Flapjack.WordRegImm.imm 0#64) sourceBody819_20 sourceBody819_0

def sourceBody819_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody819_21 sourceBody819_8

def sourceBody819_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody819_22 sourceBody819_0

def sourceBody819_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody819_10 sourceBody819_23

def sourceBody819_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody819_9 sourceBody819_24

def sourceBody819_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody819_4 sourceBody819_25

def sourceBody819_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody819_3 sourceBody819_26

def sourceBody819_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 600#64)

def sourceBody819_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody819_30 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody819_0, 819, 2)) (some 466) ([12]) (some (12, sourceBody819_29, 819, 3))

def sourceBody819_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody819_30 sourceBody819_8

def sourceBody819_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody819_31 sourceBody819_0

def sourceBody819_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody819_28 sourceBody819_32

def sourceBody819_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody819_0 sourceBody819_33

def sourceBody819_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody819_0 sourceBody819_34

def sourceBody819_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody819_27 sourceBody819_35

def sourceBody819_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 256#64)

def sourceBody819_38 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody819_0, 819, 4)) (some 68) ([12]) (some (12, sourceBody819_29, 819, 5))

def sourceBody819_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody819_38 sourceBody819_8

def sourceBody819_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody819_39 sourceBody819_0

def sourceBody819_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody819_37 sourceBody819_40

def sourceBody819_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 88#64]))

def sourceBody819_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 4)

def sourceBody819_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody819_45 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody819_0, 819, 6)) (some 808) ([8, 16]) (some (8, sourceBody819_44, 819, 7))

def sourceBody819_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody819_45 sourceBody819_8

def sourceBody819_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody819_46 sourceBody819_0

def sourceBody819_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody819_43 sourceBody819_47

def sourceBody819_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody819_42 sourceBody819_48

def sourceBody819_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody819_51 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody819_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody819_53 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 16 (Flapjack.WordRegImm.reg 2) sourceBody819_51 sourceBody819_52

def sourceBody819_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody819_53 sourceBody819_8

def sourceBody819_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 16)

def sourceBody819_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 10#64)

def sourceBody819_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 8)

def sourceBody819_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody819_57 sourceBody819_0

def sourceBody819_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody819_58 sourceBody819_0

def sourceBody819_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody819_56 sourceBody819_59

def sourceBody819_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody819_0 sourceBody819_60

def sourceBody819_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 8#64)

def sourceBody819_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody819_62 sourceBody819_44

def sourceBody819_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody819_61 sourceBody819_63

def sourceBody819_65 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.imm 0#64) sourceBody819_64 sourceBody819_0

def sourceBody819_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody819_65 sourceBody819_8

def sourceBody819_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody819_66 sourceBody819_0

def sourceBody819_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody819_55 sourceBody819_67

def sourceBody819_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody819_54 sourceBody819_68

def sourceBody819_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody819_50 sourceBody819_69

def sourceBody819_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody819_10 sourceBody819_70

def sourceBody819_72 : WordLangProgHOL (BitVec 64) :=
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

def sourceBody819_73 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 16)

def sourceBody819_74 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 8) 2

def sourceBody819_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody819_74 sourceBody819_0

def sourceBody819_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody819_73 sourceBody819_75

def sourceBody819_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody819_76 sourceBody819_0

def sourceBody819_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody819_43 sourceBody819_77

def sourceBody819_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody819_0 sourceBody819_78

def sourceBody819_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody819_72 sourceBody819_79

def sourceBody819_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody819_0 sourceBody819_80

def sourceBody819_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody819_71 sourceBody819_81

def sourceBody819_83 : WordLangProgHOL (BitVec 64) :=
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

def sourceBody819_84 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 256#64)

def sourceBody819_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody819_84 sourceBody819_77

def sourceBody819_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody819_0 sourceBody819_85

def sourceBody819_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody819_83 sourceBody819_86

def sourceBody819_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody819_0 sourceBody819_87

def sourceBody819_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody819_82 sourceBody819_88

def sourceBody819_90 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody819_91 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [8]

def sourceBody819_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody819_91 sourceBody819_0

def sourceBody819_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody819_90 sourceBody819_92

def sourceBody819_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody819_89 sourceBody819_93

def sourceBody819_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody819_49 sourceBody819_94

def sourceBody819_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody819_0 sourceBody819_95

def sourceBody819_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody819_0 sourceBody819_96

def sourceBody819_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody819_41 sourceBody819_97

def sourceBody819_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody819_0 sourceBody819_98

def sourceBody819_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody819_0 sourceBody819_99

def sourceBody819_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody819_36 sourceBody819_100

def sourceBody819_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody819_2 sourceBody819_101

def sourceBody819_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody819_0 sourceBody819_102

def sourceBody819_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody819_1 sourceBody819_103

def sourceBody819_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody819_0 sourceBody819_104

def source819 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (819, 1, sourceBody819_105)
end InitECandidate.Proofs.WordStages
