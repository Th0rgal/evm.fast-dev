import InitECandidate.Proofs.WordStages.Source801
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody817_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody817_1 : WordLangProgHOL (BitVec 64) :=
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

def sourceBody817_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 96#64]))

def sourceBody817_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 14)

def sourceBody817_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 256#64)

def sourceBody817_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody817_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody817_7 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.reg 8) sourceBody817_5 sourceBody817_6

def sourceBody817_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody817_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody817_7 sourceBody817_8

def sourceBody817_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 12)

def sourceBody817_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 10#64)

def sourceBody817_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 4)

def sourceBody817_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody817_12 sourceBody817_0

def sourceBody817_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody817_13 sourceBody817_0

def sourceBody817_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody817_11 sourceBody817_14

def sourceBody817_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody817_0 sourceBody817_15

def sourceBody817_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 8#64)

def sourceBody817_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 4

def sourceBody817_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody817_17 sourceBody817_18

def sourceBody817_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody817_16 sourceBody817_19

def sourceBody817_21 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 16 (Flapjack.WordRegImm.imm 0#64) sourceBody817_20 sourceBody817_0

def sourceBody817_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody817_21 sourceBody817_8

def sourceBody817_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody817_22 sourceBody817_0

def sourceBody817_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody817_10 sourceBody817_23

def sourceBody817_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody817_9 sourceBody817_24

def sourceBody817_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody817_4 sourceBody817_25

def sourceBody817_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody817_3 sourceBody817_26

def sourceBody817_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 375#64)

def sourceBody817_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody817_30 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody817_0, 817, 2)) (some 466) ([12]) (some (12, sourceBody817_29, 817, 3))

def sourceBody817_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody817_30 sourceBody817_8

def sourceBody817_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody817_31 sourceBody817_0

def sourceBody817_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody817_28 sourceBody817_32

def sourceBody817_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody817_0 sourceBody817_33

def sourceBody817_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody817_0 sourceBody817_34

def sourceBody817_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody817_27 sourceBody817_35

def sourceBody817_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 128#64)

def sourceBody817_38 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody817_0, 817, 4)) (some 68) ([12]) (some (12, sourceBody817_29, 817, 5))

def sourceBody817_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody817_38 sourceBody817_8

def sourceBody817_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody817_39 sourceBody817_0

def sourceBody817_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody817_37 sourceBody817_40

def sourceBody817_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 88#64]))

def sourceBody817_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 4)

def sourceBody817_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody817_45 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody817_0, 817, 6)) (some 806) ([8, 16]) (some (8, sourceBody817_44, 817, 7))

def sourceBody817_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody817_45 sourceBody817_8

def sourceBody817_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody817_46 sourceBody817_0

def sourceBody817_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody817_43 sourceBody817_47

def sourceBody817_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody817_42 sourceBody817_48

def sourceBody817_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody817_51 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody817_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody817_53 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 16 (Flapjack.WordRegImm.reg 2) sourceBody817_51 sourceBody817_52

def sourceBody817_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody817_53 sourceBody817_8

def sourceBody817_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 16)

def sourceBody817_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 10#64)

def sourceBody817_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 8)

def sourceBody817_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody817_57 sourceBody817_0

def sourceBody817_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody817_58 sourceBody817_0

def sourceBody817_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody817_56 sourceBody817_59

def sourceBody817_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody817_0 sourceBody817_60

def sourceBody817_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 8#64)

def sourceBody817_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody817_62 sourceBody817_44

def sourceBody817_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody817_61 sourceBody817_63

def sourceBody817_65 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.imm 0#64) sourceBody817_64 sourceBody817_0

def sourceBody817_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody817_65 sourceBody817_8

def sourceBody817_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody817_66 sourceBody817_0

def sourceBody817_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody817_55 sourceBody817_67

def sourceBody817_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody817_54 sourceBody817_68

def sourceBody817_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody817_50 sourceBody817_69

def sourceBody817_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody817_10 sourceBody817_70

def sourceBody817_72 : WordLangProgHOL (BitVec 64) :=
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

def sourceBody817_73 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 16)

def sourceBody817_74 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 8) 2

def sourceBody817_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody817_74 sourceBody817_0

def sourceBody817_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody817_73 sourceBody817_75

def sourceBody817_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody817_76 sourceBody817_0

def sourceBody817_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody817_43 sourceBody817_77

def sourceBody817_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody817_0 sourceBody817_78

def sourceBody817_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody817_72 sourceBody817_79

def sourceBody817_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody817_0 sourceBody817_80

def sourceBody817_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody817_71 sourceBody817_81

def sourceBody817_83 : WordLangProgHOL (BitVec 64) :=
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

def sourceBody817_84 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 128#64)

def sourceBody817_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody817_84 sourceBody817_77

def sourceBody817_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody817_0 sourceBody817_85

def sourceBody817_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody817_83 sourceBody817_86

def sourceBody817_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody817_0 sourceBody817_87

def sourceBody817_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody817_82 sourceBody817_88

def sourceBody817_90 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody817_91 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [8]

def sourceBody817_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody817_91 sourceBody817_0

def sourceBody817_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody817_90 sourceBody817_92

def sourceBody817_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody817_89 sourceBody817_93

def sourceBody817_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody817_49 sourceBody817_94

def sourceBody817_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody817_0 sourceBody817_95

def sourceBody817_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody817_0 sourceBody817_96

def sourceBody817_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody817_41 sourceBody817_97

def sourceBody817_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody817_0 sourceBody817_98

def sourceBody817_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody817_0 sourceBody817_99

def sourceBody817_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody817_36 sourceBody817_100

def sourceBody817_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody817_2 sourceBody817_101

def sourceBody817_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody817_0 sourceBody817_102

def sourceBody817_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody817_1 sourceBody817_103

def sourceBody817_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody817_0 sourceBody817_104

def source817 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (817, 1, sourceBody817_105)
end InitECandidate.Proofs.WordStages
