import InitECandidate.Proofs.WordStages.Source816
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody832_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody832_1 : WordLangProgHOL (BitVec 64) :=
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
        Flapjack.WordLangExpHOL.const 112#64]))

def sourceBody832_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 60
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 22, Flapjack.WordLangExpHOL.const 88#64]))

def sourceBody832_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 22, Flapjack.WordLangExpHOL.const 96#64]))

def sourceBody832_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 272#64]))

def sourceBody832_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 70 (Flapjack.WordLangExpHOL.var 60)

def sourceBody832_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 12)

def sourceBody832_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody832_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 96#64)

def sourceBody832_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 66 (Flapjack.WordLangExpHOL.var 50)

def sourceBody832_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 70

def sourceBody832_11 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln)
        Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody832_0, 832, 2)) (some 480) ([70, 6, 46, 28, 66]) (some (70, sourceBody832_10, 832, 3))

def sourceBody832_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody832_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_11 sourceBody832_12

def sourceBody832_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_13 sourceBody832_0

def sourceBody832_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_9 sourceBody832_14

def sourceBody832_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_8 sourceBody832_15

def sourceBody832_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_7 sourceBody832_16

def sourceBody832_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_6 sourceBody832_17

def sourceBody832_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_5 sourceBody832_18

def sourceBody832_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_0 sourceBody832_19

def sourceBody832_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_0 sourceBody832_20

def sourceBody832_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 50)

def sourceBody832_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 66 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody832_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 28

def sourceBody832_25 : WordLangProgHOL (BitVec 64) :=
.call (some (([32, 70, 6, 46]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln)
        Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody832_0, 832, 4)) (some 146) ([28, 66]) (some (28, sourceBody832_24, 832, 5))

def sourceBody832_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_25 sourceBody832_12

def sourceBody832_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_26 sourceBody832_0

def sourceBody832_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_23 sourceBody832_27

def sourceBody832_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_22 sourceBody832_28

def sourceBody832_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 66 (Flapjack.WordLangExpHOL.var 32)

def sourceBody832_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 70)

def sourceBody832_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.var 6)

def sourceBody832_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 46)

def sourceBody832_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 66

def sourceBody832_35 : WordLangProgHOL (BitVec 64) :=
.call (some (([28]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln)
        Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody832_0, 832, 6)) (some 458) ([66, 18, 56, 38]) (some (66, sourceBody832_34, 832, 7))

def sourceBody832_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_35 sourceBody832_12

def sourceBody832_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_36 sourceBody832_0

def sourceBody832_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_33 sourceBody832_37

def sourceBody832_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_32 sourceBody832_38

def sourceBody832_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_31 sourceBody832_39

def sourceBody832_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_30 sourceBody832_40

def sourceBody832_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 1024#64)

def sourceBody832_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.var 28)

def sourceBody832_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody832_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody832_46 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 18 (Flapjack.WordRegImm.reg 56) sourceBody832_44 sourceBody832_45

def sourceBody832_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_46 sourceBody832_12

def sourceBody832_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 18)

def sourceBody832_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 66 (Flapjack.WordLangExpHOL.const 4#64)

def sourceBody832_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 66)

def sourceBody832_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_50 sourceBody832_0

def sourceBody832_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_51 sourceBody832_0

def sourceBody832_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_49 sourceBody832_52

def sourceBody832_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_0 sourceBody832_53

def sourceBody832_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 66 (Flapjack.WordLangExpHOL.const 8#64)

def sourceBody832_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_55 sourceBody832_34

def sourceBody832_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_54 sourceBody832_56

def sourceBody832_58 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 38 (Flapjack.WordRegImm.imm 0#64) sourceBody832_57 sourceBody832_0

def sourceBody832_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_58 sourceBody832_12

def sourceBody832_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_59 sourceBody832_0

def sourceBody832_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_48 sourceBody832_60

def sourceBody832_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_47 sourceBody832_61

def sourceBody832_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_43 sourceBody832_62

def sourceBody832_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_42 sourceBody832_63

def sourceBody832_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 76
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 50, Flapjack.WordLangExpHOL.const 32#64])

def sourceBody832_66 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody832_67 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 76

def sourceBody832_68 : WordLangProgHOL (BitVec 64) :=
.call (some (([66, 18, 56, 38]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
          Flapjack.Spt.ln)
        Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody832_0, 832, 8)) (some 146) ([76, 4]) (some (76, sourceBody832_67, 832, 9))

def sourceBody832_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_68 sourceBody832_12

def sourceBody832_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_69 sourceBody832_0

def sourceBody832_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_66 sourceBody832_70

def sourceBody832_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_65 sourceBody832_71

def sourceBody832_73 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 66)

def sourceBody832_74 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 18)

def sourceBody832_75 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 56)

def sourceBody832_76 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 64 (Flapjack.WordLangExpHOL.var 38)

def sourceBody832_77 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 4

def sourceBody832_78 : WordLangProgHOL (BitVec 64) :=
.call (some (([76]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
          Flapjack.Spt.ln)
        Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody832_0, 832, 10)) (some 458) ([4, 44, 26, 64]) (some (4, sourceBody832_77, 832, 11))

def sourceBody832_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_78 sourceBody832_12

def sourceBody832_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_79 sourceBody832_0

def sourceBody832_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_76 sourceBody832_80

def sourceBody832_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_75 sourceBody832_81

def sourceBody832_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_74 sourceBody832_82

def sourceBody832_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_73 sourceBody832_83

def sourceBody832_85 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.const 1024#64)

def sourceBody832_86 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 76)

def sourceBody832_87 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody832_88 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody832_89 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 44 (Flapjack.WordRegImm.reg 26) sourceBody832_87 sourceBody832_88

def sourceBody832_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_89 sourceBody832_12

def sourceBody832_91 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 64 (Flapjack.WordLangExpHOL.var 44)

def sourceBody832_92 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 4#64)

def sourceBody832_93 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 4)

def sourceBody832_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_93 sourceBody832_0

def sourceBody832_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_94 sourceBody832_0

def sourceBody832_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_92 sourceBody832_95

def sourceBody832_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_0 sourceBody832_96

def sourceBody832_98 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 8#64)

def sourceBody832_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_98 sourceBody832_77

def sourceBody832_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_97 sourceBody832_99

def sourceBody832_101 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 64 (Flapjack.WordRegImm.imm 0#64) sourceBody832_100 sourceBody832_0

def sourceBody832_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_101 sourceBody832_12

def sourceBody832_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_102 sourceBody832_0

def sourceBody832_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_91 sourceBody832_103

def sourceBody832_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_90 sourceBody832_104

def sourceBody832_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_86 sourceBody832_105

def sourceBody832_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_85 sourceBody832_106

def sourceBody832_108 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 50, Flapjack.WordLangExpHOL.const 64#64])

def sourceBody832_109 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody832_110 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody832_111 : WordLangProgHOL (BitVec 64) :=
.call (some (([4, 44, 26, 64]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
          PUnit.unit Flapjack.Spt.ln)
        Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody832_0, 832, 12)) (some 146) ([16, 54]) (some (16, sourceBody832_110, 832, 13))

def sourceBody832_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_111 sourceBody832_12

def sourceBody832_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_112 sourceBody832_0

def sourceBody832_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_109 sourceBody832_113

def sourceBody832_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_108 sourceBody832_114

def sourceBody832_116 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 4)

def sourceBody832_117 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 44)

def sourceBody832_118 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 74 (Flapjack.WordLangExpHOL.var 26)

def sourceBody832_119 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 64)

def sourceBody832_120 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 54

def sourceBody832_121 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
          PUnit.unit Flapjack.Spt.ln)
        Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody832_0, 832, 14)) (some 458) ([54, 36, 74, 10]) (some (54, sourceBody832_120, 832, 15))

def sourceBody832_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_121 sourceBody832_12

def sourceBody832_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_122 sourceBody832_0

def sourceBody832_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_119 sourceBody832_123

def sourceBody832_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_118 sourceBody832_124

def sourceBody832_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_117 sourceBody832_125

def sourceBody832_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_116 sourceBody832_126

def sourceBody832_128 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.const 1024#64)

def sourceBody832_129 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 74 (Flapjack.WordLangExpHOL.var 16)

def sourceBody832_130 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody832_131 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody832_132 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 36 (Flapjack.WordRegImm.reg 74) sourceBody832_130 sourceBody832_131

def sourceBody832_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_132 sourceBody832_12

def sourceBody832_134 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 36)

def sourceBody832_135 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.const 4#64)

def sourceBody832_136 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 54)

def sourceBody832_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_136 sourceBody832_0

def sourceBody832_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_137 sourceBody832_0

def sourceBody832_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_135 sourceBody832_138

def sourceBody832_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_0 sourceBody832_139

def sourceBody832_141 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.const 8#64)

def sourceBody832_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_141 sourceBody832_120

def sourceBody832_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_140 sourceBody832_142

def sourceBody832_144 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.imm 0#64) sourceBody832_143 sourceBody832_0

def sourceBody832_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_144 sourceBody832_12

def sourceBody832_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_145 sourceBody832_0

def sourceBody832_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_134 sourceBody832_146

def sourceBody832_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_133 sourceBody832_147

def sourceBody832_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_129 sourceBody832_148

def sourceBody832_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_128 sourceBody832_149

def sourceBody832_151 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.const 96#64, Flapjack.WordLangExpHOL.var 28])

def sourceBody832_152 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 74 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody832_153 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 76)

def sourceBody832_154 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 74

def sourceBody832_155 : WordLangProgHOL (BitVec 64) :=
.call (some (([36]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
          PUnit.unit Flapjack.Spt.ln)
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody832_0, 832, 16)) (some 92) ([74, 10]) (some (74, sourceBody832_154, 832, 17))

def sourceBody832_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_155 sourceBody832_12

def sourceBody832_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_156 sourceBody832_0

def sourceBody832_158 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_153 sourceBody832_157

def sourceBody832_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_152 sourceBody832_158

def sourceBody832_160 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 60)

def sourceBody832_161 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 12)

def sourceBody832_162 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 54)

def sourceBody832_163 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 68 (Flapjack.WordLangExpHOL.var 36)

def sourceBody832_164 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 50)

def sourceBody832_165 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody832_166 : WordLangProgHOL (BitVec 64) :=
.call (some (([74]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
          PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody832_0, 832, 18)) (some 480) ([10, 48, 30, 68, 20]) (some (10, sourceBody832_165, 832, 19))

def sourceBody832_167 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_166 sourceBody832_12

def sourceBody832_168 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_167 sourceBody832_0

def sourceBody832_169 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_164 sourceBody832_168

def sourceBody832_170 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_163 sourceBody832_169

def sourceBody832_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_162 sourceBody832_170

def sourceBody832_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_161 sourceBody832_171

def sourceBody832_173 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_160 sourceBody832_172

def sourceBody832_174 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_0 sourceBody832_173

def sourceBody832_175 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_0 sourceBody832_174

def sourceBody832_176 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 68 (Flapjack.WordLangExpHOL.var 50)

def sourceBody832_177 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 36)

def sourceBody832_178 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 68

def sourceBody832_179 : WordLangProgHOL (BitVec 64) :=
.call (some (([74, 10, 48, 30]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        Flapjack.Spt.ln)
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
          PUnit.unit Flapjack.Spt.ln)
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody832_0, 832, 20)) (some 146) ([68, 20]) (some (68, sourceBody832_178, 832, 21))

def sourceBody832_180 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_179 sourceBody832_12

def sourceBody832_181 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_180 sourceBody832_0

def sourceBody832_182 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_177 sourceBody832_181

def sourceBody832_183 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_176 sourceBody832_182

def sourceBody832_184 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 28)

def sourceBody832_185 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.var 16)

def sourceBody832_186 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 76)

def sourceBody832_187 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 78 (Flapjack.WordLangExpHOL.var 74)

def sourceBody832_188 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 10)

def sourceBody832_189 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 48)

def sourceBody832_190 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 30)

def sourceBody832_191 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody832_192 : WordLangProgHOL (BitVec 64) :=
.call (some (([68]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        Flapjack.Spt.ln)
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
          PUnit.unit Flapjack.Spt.ln)
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody832_0, 832, 22)) (some 831) ([20, 58, 40, 78, 2, 42, 24]) (some (20, sourceBody832_191, 832, 23))

def sourceBody832_193 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_192 sourceBody832_12

def sourceBody832_194 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_193 sourceBody832_0

def sourceBody832_195 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_190 sourceBody832_194

def sourceBody832_196 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_189 sourceBody832_195

def sourceBody832_197 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_188 sourceBody832_196

def sourceBody832_198 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_187 sourceBody832_197

def sourceBody832_199 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_186 sourceBody832_198

def sourceBody832_200 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_185 sourceBody832_199

def sourceBody832_201 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_184 sourceBody832_200

def sourceBody832_202 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.var 68)

def sourceBody832_203 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 58

def sourceBody832_204 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        Flapjack.Spt.ln)
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
          PUnit.unit Flapjack.Spt.ln)
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody832_0, 832, 24)) (some 466) ([58]) (some (58, sourceBody832_203, 832, 25))

def sourceBody832_205 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_204 sourceBody832_12

def sourceBody832_206 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_205 sourceBody832_0

def sourceBody832_207 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_202 sourceBody832_206

def sourceBody832_208 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_0 sourceBody832_207

def sourceBody832_209 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_0 sourceBody832_208

def sourceBody832_210 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.var 28)

def sourceBody832_211 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody832_212 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody832_213 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody832_214 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 58 (Flapjack.WordRegImm.reg 40) sourceBody832_212 sourceBody832_213

def sourceBody832_215 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_214 sourceBody832_12

def sourceBody832_216 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody832_217 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 58)

def sourceBody832_218 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody832_219 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 2 (Flapjack.WordRegImm.reg 42) sourceBody832_218 sourceBody832_216

def sourceBody832_220 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_219 sourceBody832_12

def sourceBody832_221 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 62 (Flapjack.WordLangExpHOL.var 16)

def sourceBody832_222 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody832_223 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 62 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody832_224 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 62 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody832_225 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 62 (Flapjack.WordRegImm.reg 14) sourceBody832_223 sourceBody832_224

def sourceBody832_226 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_225 sourceBody832_12

def sourceBody832_227 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody832_228 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 72 (Flapjack.WordLangExpHOL.var 62)

def sourceBody832_229 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody832_230 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 34 (Flapjack.WordRegImm.reg 72) sourceBody832_229 sourceBody832_227

def sourceBody832_231 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_230 sourceBody832_12

def sourceBody832_232 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.var 34])

def sourceBody832_233 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.const 8#64)

def sourceBody832_234 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody832_0, 832, 26)) (some 68) ([58]) (some (58, sourceBody832_203, 832, 27))

def sourceBody832_235 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_234 sourceBody832_12

def sourceBody832_236 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_235 sourceBody832_0

def sourceBody832_237 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_233 sourceBody832_236

def sourceBody832_238 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 256#64]),
      Flapjack.WordLangExpHOL.const 120#64])

def sourceBody832_239 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 20)

def sourceBody832_240 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 78 (Flapjack.WordLangExpHOL.var 40)

def sourceBody832_241 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 58) 78

def sourceBody832_242 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_241 sourceBody832_0

def sourceBody832_243 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_240 sourceBody832_242

def sourceBody832_244 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_243 sourceBody832_0

def sourceBody832_245 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_239 sourceBody832_244

def sourceBody832_246 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_0 sourceBody832_245

def sourceBody832_247 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_238 sourceBody832_246

def sourceBody832_248 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_0 sourceBody832_247

def sourceBody832_249 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 256#64]),
      Flapjack.WordLangExpHOL.const 128#64])

def sourceBody832_250 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_211 sourceBody832_244

def sourceBody832_251 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_0 sourceBody832_250

def sourceBody832_252 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_249 sourceBody832_251

def sourceBody832_253 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_0 sourceBody832_252

def sourceBody832_254 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_248 sourceBody832_253

def sourceBody832_255 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [58]

def sourceBody832_256 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_255 sourceBody832_0

def sourceBody832_257 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_213 sourceBody832_256

def sourceBody832_258 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_254 sourceBody832_257

def sourceBody832_259 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_237 sourceBody832_258

def sourceBody832_260 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_0 sourceBody832_259

def sourceBody832_261 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_0 sourceBody832_260

def sourceBody832_262 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.WordRegImm.imm 0#64) sourceBody832_261 sourceBody832_0

def sourceBody832_263 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_262 sourceBody832_12

def sourceBody832_264 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_263 sourceBody832_0

def sourceBody832_265 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_232 sourceBody832_264

def sourceBody832_266 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_231 sourceBody832_265

def sourceBody832_267 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_228 sourceBody832_266

def sourceBody832_268 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_227 sourceBody832_267

def sourceBody832_269 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_226 sourceBody832_268

def sourceBody832_270 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_222 sourceBody832_269

def sourceBody832_271 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_221 sourceBody832_270

def sourceBody832_272 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_220 sourceBody832_271

def sourceBody832_273 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_217 sourceBody832_272

def sourceBody832_274 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_216 sourceBody832_273

def sourceBody832_275 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_215 sourceBody832_274

def sourceBody832_276 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_211 sourceBody832_275

def sourceBody832_277 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_210 sourceBody832_276

def sourceBody832_278 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_209 sourceBody832_277

def sourceBody832_279 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 16, Flapjack.WordLangExpHOL.const 8#64])

def sourceBody832_280 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        Flapjack.Spt.ln)
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
          PUnit.unit Flapjack.Spt.ln)
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody832_0, 832, 28)) (some 68) ([58]) (some (58, sourceBody832_203, 832, 29))

def sourceBody832_281 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_280 sourceBody832_12

def sourceBody832_282 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_281 sourceBody832_0

def sourceBody832_283 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_279 sourceBody832_282

def sourceBody832_284 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 40

def sourceBody832_285 : WordLangProgHOL (BitVec 64) :=
.call (some (([58]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        Flapjack.Spt.ln)
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
          PUnit.unit (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody832_0, 832, 30)) (some 69) ([]) (some (40, sourceBody832_284, 832, 31))

def sourceBody832_286 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_285 sourceBody832_12

def sourceBody832_287 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_286 sourceBody832_0

def sourceBody832_288 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 78
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 28, Flapjack.WordLangExpHOL.const 8#64])

def sourceBody832_289 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 78

def sourceBody832_290 : WordLangProgHOL (BitVec 64) :=
.call (some (([40]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
          PUnit.unit (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody832_0, 832, 32)) (some 68) ([78]) (some (78, sourceBody832_289, 832, 33))

def sourceBody832_291 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_290 sourceBody832_12

def sourceBody832_292 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_291 sourceBody832_0

def sourceBody832_293 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_288 sourceBody832_292

def sourceBody832_294 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 76, Flapjack.WordLangExpHOL.const 8#64])

def sourceBody832_295 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 2

def sourceBody832_296 : WordLangProgHOL (BitVec 64) :=
.call (some (([78]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
          PUnit.unit (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody832_0, 832, 34)) (some 68) ([2]) (some (2, sourceBody832_295, 832, 35))

def sourceBody832_297 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_296 sourceBody832_12

def sourceBody832_298 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_297 sourceBody832_0

def sourceBody832_299 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_294 sourceBody832_298

def sourceBody832_300 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 16, Flapjack.WordLangExpHOL.const 8#64])

def sourceBody832_301 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 42

def sourceBody832_302 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
          PUnit.unit (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody832_0, 832, 36)) (some 68) ([42]) (some (42, sourceBody832_301, 832, 37))

def sourceBody832_303 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_302 sourceBody832_12

def sourceBody832_304 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_303 sourceBody832_0

def sourceBody832_305 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_300 sourceBody832_304

def sourceBody832_306 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 60)

def sourceBody832_307 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 62 (Flapjack.WordLangExpHOL.var 12)

def sourceBody832_308 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 96#64)

def sourceBody832_309 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.var 28)

def sourceBody832_310 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 40)

def sourceBody832_311 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 24

def sourceBody832_312 : WordLangProgHOL (BitVec 64) :=
.call (some (([42]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
          PUnit.unit (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody832_0, 832, 38)) (some 480) ([24, 62, 14, 52, 34]) (some (24, sourceBody832_311, 832, 39))

def sourceBody832_313 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_312 sourceBody832_12

def sourceBody832_314 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_313 sourceBody832_0

def sourceBody832_315 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_310 sourceBody832_314

def sourceBody832_316 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_309 sourceBody832_315

def sourceBody832_317 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_308 sourceBody832_316

def sourceBody832_318 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_307 sourceBody832_317

def sourceBody832_319 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_306 sourceBody832_318

def sourceBody832_320 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_0 sourceBody832_319

def sourceBody832_321 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_0 sourceBody832_320

def sourceBody832_322 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 54)

def sourceBody832_323 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.var 76)

def sourceBody832_324 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 78)

def sourceBody832_325 : WordLangProgHOL (BitVec 64) :=
.call (some (([42]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
          PUnit.unit (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody832_0, 832, 40)) (some 480) ([24, 62, 14, 52, 34]) (some (24, sourceBody832_311, 832, 41))

def sourceBody832_326 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_325 sourceBody832_12

def sourceBody832_327 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_326 sourceBody832_0

def sourceBody832_328 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_324 sourceBody832_327

def sourceBody832_329 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_323 sourceBody832_328

def sourceBody832_330 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_322 sourceBody832_329

def sourceBody832_331 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_307 sourceBody832_330

def sourceBody832_332 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_306 sourceBody832_331

def sourceBody832_333 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_0 sourceBody832_332

def sourceBody832_334 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_0 sourceBody832_333

def sourceBody832_335 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_321 sourceBody832_334

def sourceBody832_336 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 54, Flapjack.WordLangExpHOL.var 76])

def sourceBody832_337 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.var 16)

def sourceBody832_338 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 2)

def sourceBody832_339 : WordLangProgHOL (BitVec 64) :=
.call (some (([42]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
          Flapjack.Spt.ln)
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
          (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody832_0, 832, 42)) (some 480) ([24, 62, 14, 52, 34]) (some (24, sourceBody832_311, 832, 43))

def sourceBody832_340 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_339 sourceBody832_12

def sourceBody832_341 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_340 sourceBody832_0

def sourceBody832_342 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_338 sourceBody832_341

def sourceBody832_343 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_337 sourceBody832_342

def sourceBody832_344 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_336 sourceBody832_343

def sourceBody832_345 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_307 sourceBody832_344

def sourceBody832_346 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_306 sourceBody832_345

def sourceBody832_347 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_0 sourceBody832_346

def sourceBody832_348 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_0 sourceBody832_347

def sourceBody832_349 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_335 sourceBody832_348

def sourceBody832_350 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 40)

def sourceBody832_351 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 62 (Flapjack.WordLangExpHOL.var 28)

def sourceBody832_352 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 78)

def sourceBody832_353 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 72 (Flapjack.WordLangExpHOL.var 16)

def sourceBody832_354 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 20)

def sourceBody832_355 : WordLangProgHOL (BitVec 64) :=
.call (some (([42]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody832_0, 832, 44)) (some 637) ([24, 62, 14, 52, 34, 72, 8]) (some (24, sourceBody832_311, 832, 45))

def sourceBody832_356 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_355 sourceBody832_12

def sourceBody832_357 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_356 sourceBody832_0

def sourceBody832_358 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_354 sourceBody832_357

def sourceBody832_359 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_353 sourceBody832_358

def sourceBody832_360 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_338 sourceBody832_359

def sourceBody832_361 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_323 sourceBody832_360

def sourceBody832_362 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_352 sourceBody832_361

def sourceBody832_363 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_351 sourceBody832_362

def sourceBody832_364 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_350 sourceBody832_363

def sourceBody832_365 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_0 sourceBody832_364

def sourceBody832_366 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_0 sourceBody832_365

def sourceBody832_367 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_349 sourceBody832_366

def sourceBody832_368 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 58)

def sourceBody832_369 : WordLangProgHOL (BitVec 64) :=
.call (some (([42]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody832_0, 832, 46)) (some 70) ([24]) (some (24, sourceBody832_311, 832, 47))

def sourceBody832_370 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_369 sourceBody832_12

def sourceBody832_371 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_370 sourceBody832_0

def sourceBody832_372 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_368 sourceBody832_371

def sourceBody832_373 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_0 sourceBody832_372

def sourceBody832_374 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_0 sourceBody832_373

def sourceBody832_375 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_367 sourceBody832_374

def sourceBody832_376 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 256#64]),
      Flapjack.WordLangExpHOL.const 120#64])

def sourceBody832_377 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 20)

def sourceBody832_378 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 62 (Flapjack.WordLangExpHOL.var 24)

def sourceBody832_379 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 42) 62

def sourceBody832_380 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_379 sourceBody832_0

def sourceBody832_381 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_378 sourceBody832_380

def sourceBody832_382 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_381 sourceBody832_0

def sourceBody832_383 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_377 sourceBody832_382

def sourceBody832_384 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_0 sourceBody832_383

def sourceBody832_385 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_376 sourceBody832_384

def sourceBody832_386 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_0 sourceBody832_385

def sourceBody832_387 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_375 sourceBody832_386

def sourceBody832_388 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 256#64]),
      Flapjack.WordLangExpHOL.const 128#64])

def sourceBody832_389 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 16)

def sourceBody832_390 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_389 sourceBody832_382

def sourceBody832_391 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_0 sourceBody832_390

def sourceBody832_392 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_388 sourceBody832_391

def sourceBody832_393 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_0 sourceBody832_392

def sourceBody832_394 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_387 sourceBody832_393

def sourceBody832_395 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody832_396 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [42]

def sourceBody832_397 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_396 sourceBody832_0

def sourceBody832_398 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_395 sourceBody832_397

def sourceBody832_399 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_394 sourceBody832_398

def sourceBody832_400 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_305 sourceBody832_399

def sourceBody832_401 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_0 sourceBody832_400

def sourceBody832_402 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_0 sourceBody832_401

def sourceBody832_403 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_299 sourceBody832_402

def sourceBody832_404 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_0 sourceBody832_403

def sourceBody832_405 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_0 sourceBody832_404

def sourceBody832_406 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_293 sourceBody832_405

def sourceBody832_407 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_0 sourceBody832_406

def sourceBody832_408 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_0 sourceBody832_407

def sourceBody832_409 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_287 sourceBody832_408

def sourceBody832_410 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_0 sourceBody832_409

def sourceBody832_411 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_0 sourceBody832_410

def sourceBody832_412 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_283 sourceBody832_411

def sourceBody832_413 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_0 sourceBody832_412

def sourceBody832_414 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_0 sourceBody832_413

def sourceBody832_415 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_278 sourceBody832_414

def sourceBody832_416 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_201 sourceBody832_415

def sourceBody832_417 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_0 sourceBody832_416

def sourceBody832_418 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_0 sourceBody832_417

def sourceBody832_419 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_183 sourceBody832_418

def sourceBody832_420 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_0 sourceBody832_419

def sourceBody832_421 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_0 sourceBody832_420

def sourceBody832_422 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_0 sourceBody832_421

def sourceBody832_423 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_0 sourceBody832_422

def sourceBody832_424 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_0 sourceBody832_423

def sourceBody832_425 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_0 sourceBody832_424

def sourceBody832_426 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_0 sourceBody832_425

def sourceBody832_427 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_0 sourceBody832_426

def sourceBody832_428 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_175 sourceBody832_427

def sourceBody832_429 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_159 sourceBody832_428

def sourceBody832_430 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_0 sourceBody832_429

def sourceBody832_431 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_0 sourceBody832_430

def sourceBody832_432 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_151 sourceBody832_431

def sourceBody832_433 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_0 sourceBody832_432

def sourceBody832_434 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_150 sourceBody832_433

def sourceBody832_435 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_127 sourceBody832_434

def sourceBody832_436 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_0 sourceBody832_435

def sourceBody832_437 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_0 sourceBody832_436

def sourceBody832_438 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_115 sourceBody832_437

def sourceBody832_439 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_0 sourceBody832_438

def sourceBody832_440 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_0 sourceBody832_439

def sourceBody832_441 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_0 sourceBody832_440

def sourceBody832_442 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_0 sourceBody832_441

def sourceBody832_443 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_0 sourceBody832_442

def sourceBody832_444 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_0 sourceBody832_443

def sourceBody832_445 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_0 sourceBody832_444

def sourceBody832_446 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_0 sourceBody832_445

def sourceBody832_447 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_107 sourceBody832_446

def sourceBody832_448 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_84 sourceBody832_447

def sourceBody832_449 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_0 sourceBody832_448

def sourceBody832_450 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_0 sourceBody832_449

def sourceBody832_451 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_72 sourceBody832_450

def sourceBody832_452 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_0 sourceBody832_451

def sourceBody832_453 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_0 sourceBody832_452

def sourceBody832_454 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_0 sourceBody832_453

def sourceBody832_455 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_0 sourceBody832_454

def sourceBody832_456 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_0 sourceBody832_455

def sourceBody832_457 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_0 sourceBody832_456

def sourceBody832_458 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_0 sourceBody832_457

def sourceBody832_459 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_0 sourceBody832_458

def sourceBody832_460 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_64 sourceBody832_459

def sourceBody832_461 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_41 sourceBody832_460

def sourceBody832_462 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_0 sourceBody832_461

def sourceBody832_463 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_0 sourceBody832_462

def sourceBody832_464 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_29 sourceBody832_463

def sourceBody832_465 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_0 sourceBody832_464

def sourceBody832_466 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_0 sourceBody832_465

def sourceBody832_467 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_0 sourceBody832_466

def sourceBody832_468 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_0 sourceBody832_467

def sourceBody832_469 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_0 sourceBody832_468

def sourceBody832_470 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_0 sourceBody832_469

def sourceBody832_471 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_0 sourceBody832_470

def sourceBody832_472 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_0 sourceBody832_471

def sourceBody832_473 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_21 sourceBody832_472

def sourceBody832_474 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_4 sourceBody832_473

def sourceBody832_475 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_0 sourceBody832_474

def sourceBody832_476 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_3 sourceBody832_475

def sourceBody832_477 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_0 sourceBody832_476

def sourceBody832_478 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_2 sourceBody832_477

def sourceBody832_479 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_0 sourceBody832_478

def sourceBody832_480 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_1 sourceBody832_479

def sourceBody832_481 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody832_0 sourceBody832_480

def source832 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (832, 1, sourceBody832_481)
end InitECandidate.Proofs.WordStages
