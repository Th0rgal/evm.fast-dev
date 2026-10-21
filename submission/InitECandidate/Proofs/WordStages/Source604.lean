import InitECandidate.Proofs.WordStages.Source588
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody604_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody604_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody604_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln, Flapjack.Spt.ln)), sourceBody604_0, 604, 2)) (some 386) ([]) (some (18, sourceBody604_1, 604, 3))

def sourceBody604_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody604_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_2 sourceBody604_3

def sourceBody604_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_4 sourceBody604_0

def sourceBody604_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 32#64]))

def sourceBody604_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 18)

def sourceBody604_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody604_9 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody604_0, 604, 4)) (some 417) ([16]) (some (16, sourceBody604_8, 604, 5))

def sourceBody604_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_9 sourceBody604_3

def sourceBody604_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_10 sourceBody604_0

def sourceBody604_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_7 sourceBody604_11

def sourceBody604_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_0 sourceBody604_12

def sourceBody604_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_0 sourceBody604_13

def sourceBody604_15 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody604_0, 604, 6)) (some 421) ([16]) (some (16, sourceBody604_8, 604, 7))

def sourceBody604_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_15 sourceBody604_3

def sourceBody604_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_16 sourceBody604_0

def sourceBody604_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_7 sourceBody604_17

def sourceBody604_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_0 sourceBody604_18

def sourceBody604_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_0 sourceBody604_19

def sourceBody604_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_14 sourceBody604_20

def sourceBody604_22 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody604_0, 604, 8)) (some 426) ([16]) (some (16, sourceBody604_8, 604, 9))

def sourceBody604_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_22 sourceBody604_3

def sourceBody604_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_23 sourceBody604_0

def sourceBody604_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_7 sourceBody604_24

def sourceBody604_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_0 sourceBody604_25

def sourceBody604_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_0 sourceBody604_26

def sourceBody604_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_21 sourceBody604_27

def sourceBody604_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 2)

def sourceBody604_30 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody604_0, 604, 10)) (some 602) ([16]) (some (16, sourceBody604_8, 604, 11))

def sourceBody604_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_30 sourceBody604_3

def sourceBody604_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_31 sourceBody604_0

def sourceBody604_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_29 sourceBody604_32

def sourceBody604_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 160#64]))

def sourceBody604_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody604_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody604_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody604_38 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 12 (Flapjack.WordRegImm.reg 20) sourceBody604_36 sourceBody604_37

def sourceBody604_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_38 sourceBody604_3

def sourceBody604_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 12)

def sourceBody604_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 256#64]))

def sourceBody604_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
        [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
          Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
            (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
      Flapjack.WordLangExpHOL.const 256#64])

def sourceBody604_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 6)

def sourceBody604_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 20)

def sourceBody604_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 12) 4

def sourceBody604_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_45 sourceBody604_0

def sourceBody604_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_44 sourceBody604_46

def sourceBody604_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_47 sourceBody604_0

def sourceBody604_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_43 sourceBody604_48

def sourceBody604_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_0 sourceBody604_49

def sourceBody604_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_42 sourceBody604_50

def sourceBody604_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_0 sourceBody604_51

def sourceBody604_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 2)

def sourceBody604_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 6)

def sourceBody604_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 4

def sourceBody604_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.lookup (Flapjack.WordStore.temp 0#5))

def sourceBody604_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_56 sourceBody604_0

def sourceBody604_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_57 sourceBody604_0

def sourceBody604_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 8)

def sourceBody604_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody604_61 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody604_0, 604, 13)) (some 387) ([14]) (some (14, sourceBody604_60, 604, 14))

def sourceBody604_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_61 sourceBody604_3

def sourceBody604_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_62 sourceBody604_0

def sourceBody604_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_59 sourceBody604_63

def sourceBody604_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_0 sourceBody604_64

def sourceBody604_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_0 sourceBody604_65

def sourceBody604_67 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody604_0, 604, 15)) (some 470) ([]) (some (14, sourceBody604_60, 604, 16))

def sourceBody604_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_67 sourceBody604_3

def sourceBody604_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_68 sourceBody604_0

def sourceBody604_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_0 sourceBody604_69

def sourceBody604_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_0 sourceBody604_70

def sourceBody604_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_66 sourceBody604_71

def sourceBody604_73 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 12)

def sourceBody604_74 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody604_0, 604, 17)) (some 600) ([14]) (some (14, sourceBody604_60, 604, 18))

def sourceBody604_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_74 sourceBody604_3

def sourceBody604_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_75 sourceBody604_0

def sourceBody604_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_73 sourceBody604_76

def sourceBody604_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_0 sourceBody604_77

def sourceBody604_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_0 sourceBody604_78

def sourceBody604_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_72 sourceBody604_79

def sourceBody604_81 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 256#64]),
      Flapjack.WordLangExpHOL.const 120#64])

def sourceBody604_82 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 264#64]))

def sourceBody604_83 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 14)

def sourceBody604_84 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 4) 10

def sourceBody604_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_84 sourceBody604_0

def sourceBody604_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_83 sourceBody604_85

def sourceBody604_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_86 sourceBody604_0

def sourceBody604_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_82 sourceBody604_87

def sourceBody604_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_0 sourceBody604_88

def sourceBody604_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_81 sourceBody604_89

def sourceBody604_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_0 sourceBody604_90

def sourceBody604_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_80 sourceBody604_91

def sourceBody604_93 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 256#64]),
      Flapjack.WordLangExpHOL.const 128#64])

def sourceBody604_94 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody604_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_94 sourceBody604_87

def sourceBody604_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_0 sourceBody604_95

def sourceBody604_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_93 sourceBody604_96

def sourceBody604_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_0 sourceBody604_97

def sourceBody604_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_92 sourceBody604_98

def sourceBody604_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_58 sourceBody604_99

def sourceBody604_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_3 sourceBody604_100

def sourceBody604_102 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 4 (Flapjack.WordRegImm.imm 8#64) sourceBody604_55 sourceBody604_101

def sourceBody604_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_102 sourceBody604_3

def sourceBody604_104 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody604_0, 604, 12)) (some 603) ([4, 14]) (some (4, sourceBody604_103, 604, 19))

def sourceBody604_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_104 sourceBody604_3

def sourceBody604_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_105 sourceBody604_0

def sourceBody604_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_54 sourceBody604_106

def sourceBody604_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_53 sourceBody604_107

def sourceBody604_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_0 sourceBody604_108

def sourceBody604_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_0 sourceBody604_109

def sourceBody604_111 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
        [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
          Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
            (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
      Flapjack.WordLangExpHOL.const 256#64])

def sourceBody604_112 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 16)

def sourceBody604_113 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 4)

def sourceBody604_114 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 20) 14

def sourceBody604_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_114 sourceBody604_0

def sourceBody604_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_113 sourceBody604_115

def sourceBody604_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_116 sourceBody604_0

def sourceBody604_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_112 sourceBody604_117

def sourceBody604_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_0 sourceBody604_118

def sourceBody604_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_111 sourceBody604_119

def sourceBody604_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_0 sourceBody604_120

def sourceBody604_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_110 sourceBody604_121

def sourceBody604_123 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [20]

def sourceBody604_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_123 sourceBody604_0

def sourceBody604_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_43 sourceBody604_124

def sourceBody604_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_122 sourceBody604_125

def sourceBody604_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_0 sourceBody604_126

def sourceBody604_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_0 sourceBody604_127

def sourceBody604_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_52 sourceBody604_128

def sourceBody604_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_41 sourceBody604_129

def sourceBody604_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_0 sourceBody604_130

def sourceBody604_132 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 4 (Flapjack.WordRegImm.imm 0#64) sourceBody604_131 sourceBody604_0

def sourceBody604_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_132 sourceBody604_3

def sourceBody604_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_133 sourceBody604_0

def sourceBody604_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_40 sourceBody604_134

def sourceBody604_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_39 sourceBody604_135

def sourceBody604_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_35 sourceBody604_136

def sourceBody604_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_34 sourceBody604_137

def sourceBody604_139 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 8)

def sourceBody604_140 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody604_141 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody604_0, 604, 20)) (some 387) ([12]) (some (12, sourceBody604_140, 604, 21))

def sourceBody604_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_141 sourceBody604_3

def sourceBody604_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_142 sourceBody604_0

def sourceBody604_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_139 sourceBody604_143

def sourceBody604_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_0 sourceBody604_144

def sourceBody604_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_0 sourceBody604_145

def sourceBody604_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_138 sourceBody604_146

def sourceBody604_148 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 6)

def sourceBody604_149 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [16]

def sourceBody604_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_149 sourceBody604_0

def sourceBody604_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_148 sourceBody604_150

def sourceBody604_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_147 sourceBody604_151

def sourceBody604_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_33 sourceBody604_152

def sourceBody604_154 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_0 sourceBody604_153

def sourceBody604_155 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_0 sourceBody604_154

def sourceBody604_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_28 sourceBody604_155

def sourceBody604_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_6 sourceBody604_156

def sourceBody604_158 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_0 sourceBody604_157

def sourceBody604_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_5 sourceBody604_158

def sourceBody604_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_0 sourceBody604_159

def sourceBody604_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody604_0 sourceBody604_160

def source604 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (604, 2, sourceBody604_161)
end InitECandidate.Proofs.WordStages
