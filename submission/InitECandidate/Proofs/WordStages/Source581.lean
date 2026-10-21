import InitECandidate.Proofs.WordStages.Source565
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody581_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody581_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 6)

def sourceBody581_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 8)

def sourceBody581_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 10)

def sourceBody581_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 12)

def sourceBody581_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody581_6 : WordLangProgHOL (BitVec 64) :=
.call (some (([30]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody581_0, 581, 2)) (some 102) ([16, 24, 20, 28]) (some (16, sourceBody581_5, 581, 3))

def sourceBody581_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody581_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_6 sourceBody581_7

def sourceBody581_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_8 sourceBody581_0

def sourceBody581_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_4 sourceBody581_9

def sourceBody581_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_3 sourceBody581_10

def sourceBody581_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_2 sourceBody581_11

def sourceBody581_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_1 sourceBody581_12

def sourceBody581_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 30)

def sourceBody581_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody581_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody581_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody581_18 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 24 (Flapjack.WordRegImm.reg 20) sourceBody581_16 sourceBody581_17

def sourceBody581_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_18 sourceBody581_7

def sourceBody581_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 24)

def sourceBody581_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody581_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [16]

def sourceBody581_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_22 sourceBody581_0

def sourceBody581_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_21 sourceBody581_23

def sourceBody581_25 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 28 (Flapjack.WordRegImm.imm 0#64) sourceBody581_24 sourceBody581_0

def sourceBody581_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_25 sourceBody581_7

def sourceBody581_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_26 sourceBody581_0

def sourceBody581_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_20 sourceBody581_27

def sourceBody581_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_19 sourceBody581_28

def sourceBody581_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_15 sourceBody581_29

def sourceBody581_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_14 sourceBody581_30

def sourceBody581_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 40#64)

def sourceBody581_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 24

def sourceBody581_34 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody581_0, 581, 4)) (some 68) ([24]) (some (24, sourceBody581_33, 581, 5))

def sourceBody581_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_34 sourceBody581_7

def sourceBody581_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_35 sourceBody581_0

def sourceBody581_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_32 sourceBody581_36

def sourceBody581_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 16, Flapjack.WordLangExpHOL.const 0#64])

def sourceBody581_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 304#64]))

def sourceBody581_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 20)

def sourceBody581_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 24) 28

def sourceBody581_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_41 sourceBody581_0

def sourceBody581_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_40 sourceBody581_42

def sourceBody581_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_43 sourceBody581_0

def sourceBody581_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_39 sourceBody581_44

def sourceBody581_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_0 sourceBody581_45

def sourceBody581_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_38 sourceBody581_46

def sourceBody581_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_0 sourceBody581_47

def sourceBody581_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 96#64)

def sourceBody581_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody581_51 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody581_0, 581, 6)) (some 68) ([20]) (some (20, sourceBody581_50, 581, 7))

def sourceBody581_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_51 sourceBody581_7

def sourceBody581_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_52 sourceBody581_0

def sourceBody581_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_49 sourceBody581_53

def sourceBody581_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 296#64]))

def sourceBody581_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody581_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 28

def sourceBody581_58 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody581_0, 581, 8)) (some 77) ([28, 18, 26]) (some (28, sourceBody581_57, 581, 9))

def sourceBody581_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_58 sourceBody581_7

def sourceBody581_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_59 sourceBody581_0

def sourceBody581_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_56 sourceBody581_60

def sourceBody581_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_55 sourceBody581_61

def sourceBody581_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_20 sourceBody581_62

def sourceBody581_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_0 sourceBody581_63

def sourceBody581_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_0 sourceBody581_64

def sourceBody581_66 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 24, Flapjack.WordLangExpHOL.const 32#64])

def sourceBody581_67 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 12#64)

def sourceBody581_68 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody581_0, 581, 10)) (some 78) ([28, 18]) (some (28, sourceBody581_57, 581, 11))

def sourceBody581_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_68 sourceBody581_7

def sourceBody581_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_69 sourceBody581_0

def sourceBody581_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_67 sourceBody581_70

def sourceBody581_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_66 sourceBody581_71

def sourceBody581_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_0 sourceBody581_72

def sourceBody581_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_0 sourceBody581_73

def sourceBody581_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_65 sourceBody581_74

def sourceBody581_76 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 24, Flapjack.WordLangExpHOL.const 44#64])

def sourceBody581_77 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 2)

def sourceBody581_78 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 20#64)

def sourceBody581_79 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody581_0, 581, 12)) (some 77) ([28, 18, 26]) (some (28, sourceBody581_57, 581, 13))

def sourceBody581_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_79 sourceBody581_7

def sourceBody581_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_80 sourceBody581_0

def sourceBody581_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_78 sourceBody581_81

def sourceBody581_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_77 sourceBody581_82

def sourceBody581_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_76 sourceBody581_83

def sourceBody581_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_0 sourceBody581_84

def sourceBody581_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_0 sourceBody581_85

def sourceBody581_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_75 sourceBody581_86

def sourceBody581_88 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 24, Flapjack.WordLangExpHOL.const 64#64])

def sourceBody581_89 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody581_0, 581, 14)) (some 78) ([28, 18]) (some (28, sourceBody581_57, 581, 15))

def sourceBody581_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_89 sourceBody581_7

def sourceBody581_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_90 sourceBody581_0

def sourceBody581_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_67 sourceBody581_91

def sourceBody581_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_88 sourceBody581_92

def sourceBody581_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_0 sourceBody581_93

def sourceBody581_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_0 sourceBody581_94

def sourceBody581_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_87 sourceBody581_95

def sourceBody581_97 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 24, Flapjack.WordLangExpHOL.const 76#64])

def sourceBody581_98 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 4)

def sourceBody581_99 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody581_0, 581, 16)) (some 77) ([28, 18, 26]) (some (28, sourceBody581_57, 581, 17))

def sourceBody581_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_99 sourceBody581_7

def sourceBody581_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_100 sourceBody581_0

def sourceBody581_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_78 sourceBody581_101

def sourceBody581_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_98 sourceBody581_102

def sourceBody581_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_97 sourceBody581_103

def sourceBody581_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_0 sourceBody581_104

def sourceBody581_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_0 sourceBody581_105

def sourceBody581_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_96 sourceBody581_106

def sourceBody581_108 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 16, Flapjack.WordLangExpHOL.const 8#64])

def sourceBody581_109 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 28)

def sourceBody581_110 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 20) 18

def sourceBody581_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_110 sourceBody581_0

def sourceBody581_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_109 sourceBody581_111

def sourceBody581_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_112 sourceBody581_0

def sourceBody581_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_20 sourceBody581_113

def sourceBody581_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_0 sourceBody581_114

def sourceBody581_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_108 sourceBody581_115

def sourceBody581_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_0 sourceBody581_116

def sourceBody581_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_107 sourceBody581_117

def sourceBody581_119 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 16, Flapjack.WordLangExpHOL.const 16#64])

def sourceBody581_120 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 3#64)

def sourceBody581_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_120 sourceBody581_113

def sourceBody581_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_0 sourceBody581_121

def sourceBody581_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_119 sourceBody581_122

def sourceBody581_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_0 sourceBody581_123

def sourceBody581_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_118 sourceBody581_124

def sourceBody581_126 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody581_127 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody581_0, 581, 18)) (some 68) ([28]) (some (28, sourceBody581_57, 581, 19))

def sourceBody581_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_127 sourceBody581_7

def sourceBody581_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_128 sourceBody581_0

def sourceBody581_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_126 sourceBody581_129

def sourceBody581_131 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 6)

def sourceBody581_132 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 8)

def sourceBody581_133 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 10)

def sourceBody581_134 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 12)

def sourceBody581_135 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 20)

def sourceBody581_136 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody581_137 : WordLangProgHOL (BitVec 64) :=
.call (some (([28]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody581_0, 581, 20)) (some 147) ([18, 26, 22, 32, 14]) (some (18, sourceBody581_136, 581, 21))

def sourceBody581_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_137 sourceBody581_7

def sourceBody581_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_138 sourceBody581_0

def sourceBody581_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_135 sourceBody581_139

def sourceBody581_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_134 sourceBody581_140

def sourceBody581_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_133 sourceBody581_141

def sourceBody581_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_132 sourceBody581_142

def sourceBody581_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_131 sourceBody581_143

def sourceBody581_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_0 sourceBody581_144

def sourceBody581_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_0 sourceBody581_145

def sourceBody581_147 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 16, Flapjack.WordLangExpHOL.const 24#64])

def sourceBody581_148 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 20)

def sourceBody581_149 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 18)

def sourceBody581_150 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 28) 26

def sourceBody581_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_150 sourceBody581_0

def sourceBody581_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_149 sourceBody581_151

def sourceBody581_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_152 sourceBody581_0

def sourceBody581_154 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_148 sourceBody581_153

def sourceBody581_155 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_0 sourceBody581_154

def sourceBody581_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_147 sourceBody581_155

def sourceBody581_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_0 sourceBody581_156

def sourceBody581_158 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_146 sourceBody581_157

def sourceBody581_159 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 16, Flapjack.WordLangExpHOL.const 32#64])

def sourceBody581_160 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody581_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_160 sourceBody581_153

def sourceBody581_162 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_0 sourceBody581_161

def sourceBody581_163 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_159 sourceBody581_162

def sourceBody581_164 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_0 sourceBody581_163

def sourceBody581_165 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_158 sourceBody581_164

def sourceBody581_166 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 256#64]))

def sourceBody581_167 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 16)

def sourceBody581_168 : WordLangProgHOL (BitVec 64) :=
.call (some (([28]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody581_0, 581, 22)) (some 541) ([18, 26]) (some (18, sourceBody581_136, 581, 23))

def sourceBody581_169 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_168 sourceBody581_7

def sourceBody581_170 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_169 sourceBody581_0

def sourceBody581_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_167 sourceBody581_170

def sourceBody581_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_166 sourceBody581_171

def sourceBody581_173 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_0 sourceBody581_172

def sourceBody581_174 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_0 sourceBody581_173

def sourceBody581_175 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_165 sourceBody581_174

def sourceBody581_176 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody581_177 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [28]

def sourceBody581_178 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_177 sourceBody581_0

def sourceBody581_179 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_176 sourceBody581_178

def sourceBody581_180 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_175 sourceBody581_179

def sourceBody581_181 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_130 sourceBody581_180

def sourceBody581_182 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_0 sourceBody581_181

def sourceBody581_183 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_0 sourceBody581_182

def sourceBody581_184 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_125 sourceBody581_183

def sourceBody581_185 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_54 sourceBody581_184

def sourceBody581_186 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_0 sourceBody581_185

def sourceBody581_187 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_0 sourceBody581_186

def sourceBody581_188 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_48 sourceBody581_187

def sourceBody581_189 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_37 sourceBody581_188

def sourceBody581_190 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_0 sourceBody581_189

def sourceBody581_191 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_0 sourceBody581_190

def sourceBody581_192 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_31 sourceBody581_191

def sourceBody581_193 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_13 sourceBody581_192

def sourceBody581_194 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_0 sourceBody581_193

def sourceBody581_195 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody581_0 sourceBody581_194

def source581 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (581, 7, sourceBody581_195)
end InitECandidate.Proofs.WordStages
