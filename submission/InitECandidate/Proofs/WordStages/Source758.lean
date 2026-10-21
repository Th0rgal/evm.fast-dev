import InitECandidate.Proofs.WordStages.Source742
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody758_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody758_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 2)

def sourceBody758_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 4)

def sourceBody758_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody758_4 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody758_0, 758, 2)) (some 734) ([6, 10]) (some (6, sourceBody758_3, 758, 3))

def sourceBody758_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody758_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody758_4 sourceBody758_5

def sourceBody758_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody758_6 sourceBody758_0

def sourceBody758_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody758_2 sourceBody758_7

def sourceBody758_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody758_1 sourceBody758_8

def sourceBody758_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody758_0 sourceBody758_9

def sourceBody758_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody758_0 sourceBody758_10

def sourceBody758_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 96#64])

def sourceBody758_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 96#64])

def sourceBody758_14 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody758_0, 758, 4)) (some 734) ([6, 10]) (some (6, sourceBody758_3, 758, 5))

def sourceBody758_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody758_14 sourceBody758_5

def sourceBody758_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody758_15 sourceBody758_0

def sourceBody758_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody758_13 sourceBody758_16

def sourceBody758_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody758_12 sourceBody758_17

def sourceBody758_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody758_0 sourceBody758_18

def sourceBody758_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody758_0 sourceBody758_19

def sourceBody758_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody758_11 sourceBody758_20

def sourceBody758_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 96#64])

def sourceBody758_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 392#64]),
      Flapjack.WordLangExpHOL.const 960#64])

def sourceBody758_24 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody758_0, 758, 6)) (some 735) ([6, 10, 8]) (some (6, sourceBody758_3, 758, 7))

def sourceBody758_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody758_24 sourceBody758_5

def sourceBody758_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody758_25 sourceBody758_0

def sourceBody758_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody758_23 sourceBody758_26

def sourceBody758_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody758_22 sourceBody758_27

def sourceBody758_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody758_12 sourceBody758_28

def sourceBody758_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody758_0 sourceBody758_29

def sourceBody758_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody758_0 sourceBody758_30

def sourceBody758_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody758_21 sourceBody758_31

def sourceBody758_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 192#64])

def sourceBody758_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 192#64])

def sourceBody758_35 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody758_0, 758, 8)) (some 734) ([6, 10]) (some (6, sourceBody758_3, 758, 9))

def sourceBody758_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody758_35 sourceBody758_5

def sourceBody758_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody758_36 sourceBody758_0

def sourceBody758_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody758_34 sourceBody758_37

def sourceBody758_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody758_33 sourceBody758_38

def sourceBody758_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody758_0 sourceBody758_39

def sourceBody758_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody758_0 sourceBody758_40

def sourceBody758_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody758_32 sourceBody758_41

def sourceBody758_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 192#64])

def sourceBody758_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 392#64]),
      Flapjack.WordLangExpHOL.const 1152#64])

def sourceBody758_45 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody758_0, 758, 10)) (some 735) ([6, 10, 8]) (some (6, sourceBody758_3, 758, 11))

def sourceBody758_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody758_45 sourceBody758_5

def sourceBody758_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody758_46 sourceBody758_0

def sourceBody758_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody758_44 sourceBody758_47

def sourceBody758_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody758_43 sourceBody758_48

def sourceBody758_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody758_33 sourceBody758_49

def sourceBody758_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody758_0 sourceBody758_50

def sourceBody758_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody758_0 sourceBody758_51

def sourceBody758_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody758_42 sourceBody758_52

def sourceBody758_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 288#64])

def sourceBody758_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 288#64])

def sourceBody758_56 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody758_0, 758, 12)) (some 734) ([6, 10]) (some (6, sourceBody758_3, 758, 13))

def sourceBody758_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody758_56 sourceBody758_5

def sourceBody758_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody758_57 sourceBody758_0

def sourceBody758_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody758_55 sourceBody758_58

def sourceBody758_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody758_54 sourceBody758_59

def sourceBody758_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody758_0 sourceBody758_60

def sourceBody758_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody758_0 sourceBody758_61

def sourceBody758_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody758_53 sourceBody758_62

def sourceBody758_64 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 288#64])

def sourceBody758_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 392#64]),
      Flapjack.WordLangExpHOL.const 864#64])

def sourceBody758_66 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody758_0, 758, 14)) (some 735) ([6, 10, 8]) (some (6, sourceBody758_3, 758, 15))

def sourceBody758_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody758_66 sourceBody758_5

def sourceBody758_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody758_67 sourceBody758_0

def sourceBody758_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody758_65 sourceBody758_68

def sourceBody758_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody758_64 sourceBody758_69

def sourceBody758_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody758_54 sourceBody758_70

def sourceBody758_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody758_0 sourceBody758_71

def sourceBody758_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody758_0 sourceBody758_72

def sourceBody758_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody758_63 sourceBody758_73

def sourceBody758_75 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 384#64])

def sourceBody758_76 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 384#64])

def sourceBody758_77 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody758_0, 758, 16)) (some 734) ([6, 10]) (some (6, sourceBody758_3, 758, 17))

def sourceBody758_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody758_77 sourceBody758_5

def sourceBody758_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody758_78 sourceBody758_0

def sourceBody758_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody758_76 sourceBody758_79

def sourceBody758_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody758_75 sourceBody758_80

def sourceBody758_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody758_0 sourceBody758_81

def sourceBody758_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody758_0 sourceBody758_82

def sourceBody758_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody758_74 sourceBody758_83

def sourceBody758_85 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 384#64])

def sourceBody758_86 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 392#64]),
      Flapjack.WordLangExpHOL.const 1056#64])

def sourceBody758_87 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody758_0, 758, 18)) (some 735) ([6, 10, 8]) (some (6, sourceBody758_3, 758, 19))

def sourceBody758_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody758_87 sourceBody758_5

def sourceBody758_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody758_88 sourceBody758_0

def sourceBody758_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody758_86 sourceBody758_89

def sourceBody758_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody758_85 sourceBody758_90

def sourceBody758_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody758_75 sourceBody758_91

def sourceBody758_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody758_0 sourceBody758_92

def sourceBody758_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody758_0 sourceBody758_93

def sourceBody758_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody758_84 sourceBody758_94

def sourceBody758_96 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 480#64])

def sourceBody758_97 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 480#64])

def sourceBody758_98 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln, Flapjack.Spt.ln)), sourceBody758_0, 758, 20)) (some 734) ([6, 10]) (some (6, sourceBody758_3, 758, 21))

def sourceBody758_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody758_98 sourceBody758_5

def sourceBody758_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody758_99 sourceBody758_0

def sourceBody758_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody758_97 sourceBody758_100

def sourceBody758_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody758_96 sourceBody758_101

def sourceBody758_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody758_0 sourceBody758_102

def sourceBody758_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody758_0 sourceBody758_103

def sourceBody758_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody758_95 sourceBody758_104

def sourceBody758_106 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 480#64])

def sourceBody758_107 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 392#64]),
      Flapjack.WordLangExpHOL.const 1248#64])

def sourceBody758_108 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody758_0, 758, 22)) (some 735) ([6, 10, 8]) (some (6, sourceBody758_3, 758, 23))

def sourceBody758_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody758_108 sourceBody758_5

def sourceBody758_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody758_109 sourceBody758_0

def sourceBody758_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody758_107 sourceBody758_110

def sourceBody758_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody758_106 sourceBody758_111

def sourceBody758_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody758_96 sourceBody758_112

def sourceBody758_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody758_0 sourceBody758_113

def sourceBody758_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody758_0 sourceBody758_114

def sourceBody758_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody758_105 sourceBody758_115

def sourceBody758_117 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody758_118 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [12]

def sourceBody758_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody758_118 sourceBody758_0

def sourceBody758_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody758_117 sourceBody758_119

def sourceBody758_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody758_116 sourceBody758_120

def source758 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (758, 3, sourceBody758_121)
end InitECandidate.Proofs.WordStages
