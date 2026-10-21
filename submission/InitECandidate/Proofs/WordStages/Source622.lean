import InitECandidate.Proofs.WordStages.Source606
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody622_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 320#64]))

def sourceBody622_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody622_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody622_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody622_4 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.WordRegImm.reg 2) sourceBody622_2 sourceBody622_3

def sourceBody622_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody622_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_4 sourceBody622_5

def sourceBody622_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 8)

def sourceBody622_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody622_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [4]

def sourceBody622_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody622_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_9 sourceBody622_10

def sourceBody622_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_8 sourceBody622_11

def sourceBody622_13 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.WordRegImm.imm 0#64) sourceBody622_12 sourceBody622_10

def sourceBody622_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_13 sourceBody622_5

def sourceBody622_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_14 sourceBody622_10

def sourceBody622_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_7 sourceBody622_15

def sourceBody622_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_6 sourceBody622_16

def sourceBody622_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_1 sourceBody622_17

def sourceBody622_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_0 sourceBody622_18

def sourceBody622_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 160#64)

def sourceBody622_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody622_22 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody622_10, 622, 2)) (some 68) ([8]) (some (8, sourceBody622_21, 622, 3))

def sourceBody622_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_22 sourceBody622_5

def sourceBody622_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_23 sourceBody622_10

def sourceBody622_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_20 sourceBody622_24

def sourceBody622_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
        [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
          Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
            (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
      Flapjack.WordLangExpHOL.const 320#64])

def sourceBody622_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 4)

def sourceBody622_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 2)

def sourceBody622_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 8) 6

def sourceBody622_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_29 sourceBody622_10

def sourceBody622_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_28 sourceBody622_30

def sourceBody622_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_31 sourceBody622_10

def sourceBody622_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_27 sourceBody622_32

def sourceBody622_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_10 sourceBody622_33

def sourceBody622_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_26 sourceBody622_34

def sourceBody622_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_10 sourceBody622_35

def sourceBody622_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_25 sourceBody622_36

def sourceBody622_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_10 sourceBody622_37

def sourceBody622_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_10 sourceBody622_38

def sourceBody622_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_19 sourceBody622_39

def sourceBody622_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 128#64)

def sourceBody622_42 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody622_10, 622, 4)) (some 68) ([8]) (some (8, sourceBody622_21, 622, 5))

def sourceBody622_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_42 sourceBody622_5

def sourceBody622_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_43 sourceBody622_10

def sourceBody622_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_41 sourceBody622_44

def sourceBody622_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
        [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
          Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
            (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
      Flapjack.WordLangExpHOL.const 328#64])

def sourceBody622_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_46 sourceBody622_34

def sourceBody622_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_10 sourceBody622_47

def sourceBody622_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_45 sourceBody622_48

def sourceBody622_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_10 sourceBody622_49

def sourceBody622_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_10 sourceBody622_50

def sourceBody622_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_40 sourceBody622_51

def sourceBody622_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 40#64)

def sourceBody622_54 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody622_10, 622, 6)) (some 68) ([8]) (some (8, sourceBody622_21, 622, 7))

def sourceBody622_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_54 sourceBody622_5

def sourceBody622_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_55 sourceBody622_10

def sourceBody622_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_53 sourceBody622_56

def sourceBody622_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
        [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
          Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
            (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
      Flapjack.WordLangExpHOL.const 336#64])

def sourceBody622_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_58 sourceBody622_34

def sourceBody622_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_10 sourceBody622_59

def sourceBody622_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_57 sourceBody622_60

def sourceBody622_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_10 sourceBody622_61

def sourceBody622_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_10 sourceBody622_62

def sourceBody622_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_52 sourceBody622_63

def sourceBody622_65 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody622_10, 622, 8)) (some 68) ([8]) (some (8, sourceBody622_21, 622, 9))

def sourceBody622_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_65 sourceBody622_5

def sourceBody622_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_66 sourceBody622_10

def sourceBody622_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_41 sourceBody622_67

def sourceBody622_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
        [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
          Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
            (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
      Flapjack.WordLangExpHOL.const 344#64])

def sourceBody622_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_69 sourceBody622_34

def sourceBody622_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_10 sourceBody622_70

def sourceBody622_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_68 sourceBody622_71

def sourceBody622_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_10 sourceBody622_72

def sourceBody622_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_10 sourceBody622_73

def sourceBody622_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_64 sourceBody622_74

def sourceBody622_76 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 320#64]),
      Flapjack.WordLangExpHOL.const 0#64])

def sourceBody622_77 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 18364758544493064720#64)

def sourceBody622_78 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 8)

def sourceBody622_79 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 4) 2

def sourceBody622_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_79 sourceBody622_10

def sourceBody622_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_78 sourceBody622_80

def sourceBody622_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_81 sourceBody622_10

def sourceBody622_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_77 sourceBody622_82

def sourceBody622_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_10 sourceBody622_83

def sourceBody622_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_76 sourceBody622_84

def sourceBody622_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_10 sourceBody622_85

def sourceBody622_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_75 sourceBody622_86

def sourceBody622_88 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 320#64]),
      Flapjack.WordLangExpHOL.const 8#64])

def sourceBody622_89 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 10079716825146989895#64)

def sourceBody622_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_89 sourceBody622_82

def sourceBody622_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_10 sourceBody622_90

def sourceBody622_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_88 sourceBody622_91

def sourceBody622_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_10 sourceBody622_92

def sourceBody622_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_87 sourceBody622_93

def sourceBody622_95 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 320#64]),
      Flapjack.WordLangExpHOL.const 16#64])

def sourceBody622_96 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 14248650839231647395#64)

def sourceBody622_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_96 sourceBody622_82

def sourceBody622_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_10 sourceBody622_97

def sourceBody622_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_95 sourceBody622_98

def sourceBody622_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_10 sourceBody622_99

def sourceBody622_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_94 sourceBody622_100

def sourceBody622_102 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 320#64]),
      Flapjack.WordLangExpHOL.const 24#64])

def sourceBody622_103 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 2764919063900629905#64)

def sourceBody622_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_103 sourceBody622_82

def sourceBody622_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_10 sourceBody622_104

def sourceBody622_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_102 sourceBody622_105

def sourceBody622_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_10 sourceBody622_106

def sourceBody622_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_101 sourceBody622_107

def sourceBody622_109 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 320#64]),
      Flapjack.WordLangExpHOL.const 32#64])

def sourceBody622_110 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 16099105460569216260#64)

def sourceBody622_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_110 sourceBody622_82

def sourceBody622_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_10 sourceBody622_111

def sourceBody622_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_109 sourceBody622_112

def sourceBody622_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_10 sourceBody622_113

def sourceBody622_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_108 sourceBody622_114

def sourceBody622_116 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 320#64]),
      Flapjack.WordLangExpHOL.const 40#64])

def sourceBody622_117 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 14096706008221550565#64)

def sourceBody622_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_117 sourceBody622_82

def sourceBody622_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_10 sourceBody622_118

def sourceBody622_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_116 sourceBody622_119

def sourceBody622_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_10 sourceBody622_120

def sourceBody622_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_115 sourceBody622_121

def sourceBody622_123 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 320#64]),
      Flapjack.WordLangExpHOL.const 48#64])

def sourceBody622_124 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 2419779895833949110#64)

def sourceBody622_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_124 sourceBody622_82

def sourceBody622_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_10 sourceBody622_125

def sourceBody622_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_123 sourceBody622_126

def sourceBody622_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_10 sourceBody622_127

def sourceBody622_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_122 sourceBody622_128

def sourceBody622_130 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 320#64]),
      Flapjack.WordLangExpHOL.const 56#64])

def sourceBody622_131 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 15279073663851639135#64)

def sourceBody622_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_131 sourceBody622_82

def sourceBody622_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_10 sourceBody622_132

def sourceBody622_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_130 sourceBody622_133

def sourceBody622_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_10 sourceBody622_134

def sourceBody622_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_129 sourceBody622_135

def sourceBody622_137 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 320#64]),
      Flapjack.WordLangExpHOL.const 64#64])

def sourceBody622_138 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 16895767220870911080#64)

def sourceBody622_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_138 sourceBody622_82

def sourceBody622_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_10 sourceBody622_139

def sourceBody622_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_137 sourceBody622_140

def sourceBody622_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_10 sourceBody622_141

def sourceBody622_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_136 sourceBody622_142

def sourceBody622_144 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 320#64]),
      Flapjack.WordLangExpHOL.const 72#64])

def sourceBody622_145 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 13344426445381913340#64)

def sourceBody622_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_145 sourceBody622_82

def sourceBody622_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_10 sourceBody622_146

def sourceBody622_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_144 sourceBody622_147

def sourceBody622_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_10 sourceBody622_148

def sourceBody622_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_143 sourceBody622_149

def sourceBody622_151 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 320#64]),
      Flapjack.WordLangExpHOL.const 80#64])

def sourceBody622_152 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 9905384649541406699#64)

def sourceBody622_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_152 sourceBody622_82

def sourceBody622_154 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_10 sourceBody622_153

def sourceBody622_155 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_151 sourceBody622_154

def sourceBody622_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_10 sourceBody622_155

def sourceBody622_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_150 sourceBody622_156

def sourceBody622_158 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 320#64]),
      Flapjack.WordLangExpHOL.const 88#64])

def sourceBody622_159 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 14806603881112131687#64)

def sourceBody622_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_159 sourceBody622_82

def sourceBody622_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_10 sourceBody622_160

def sourceBody622_162 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_158 sourceBody622_161

def sourceBody622_163 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_10 sourceBody622_162

def sourceBody622_164 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_157 sourceBody622_163

def sourceBody622_165 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 320#64]),
      Flapjack.WordLangExpHOL.const 96#64])

def sourceBody622_166 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 6324581712619534043#64)

def sourceBody622_167 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_166 sourceBody622_82

def sourceBody622_168 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_10 sourceBody622_167

def sourceBody622_169 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_165 sourceBody622_168

def sourceBody622_170 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_10 sourceBody622_169

def sourceBody622_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_164 sourceBody622_170

def sourceBody622_172 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 320#64]),
      Flapjack.WordLangExpHOL.const 104#64])

def sourceBody622_173 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 14224731476766686923#64)

def sourceBody622_174 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_173 sourceBody622_82

def sourceBody622_175 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_10 sourceBody622_174

def sourceBody622_176 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_172 sourceBody622_175

def sourceBody622_177 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_10 sourceBody622_176

def sourceBody622_178 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_171 sourceBody622_177

def sourceBody622_179 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 320#64]),
      Flapjack.WordLangExpHOL.const 112#64])

def sourceBody622_180 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 7317203453406000633#64)

def sourceBody622_181 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_180 sourceBody622_82

def sourceBody622_182 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_10 sourceBody622_181

def sourceBody622_183 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_179 sourceBody622_182

def sourceBody622_184 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_10 sourceBody622_183

def sourceBody622_185 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_178 sourceBody622_184

def sourceBody622_186 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 320#64]),
      Flapjack.WordLangExpHOL.const 120#64])

def sourceBody622_187 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 7849414023404435864#64)

def sourceBody622_188 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_187 sourceBody622_82

def sourceBody622_189 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_10 sourceBody622_188

def sourceBody622_190 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_186 sourceBody622_189

def sourceBody622_191 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_10 sourceBody622_190

def sourceBody622_192 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_185 sourceBody622_191

def sourceBody622_193 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 320#64]),
      Flapjack.WordLangExpHOL.const 128#64])

def sourceBody622_194 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 13688264971095146457#64)

def sourceBody622_195 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_194 sourceBody622_82

def sourceBody622_196 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_10 sourceBody622_195

def sourceBody622_197 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_193 sourceBody622_196

def sourceBody622_198 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_10 sourceBody622_197

def sourceBody622_199 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_192 sourceBody622_198

def sourceBody622_200 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 320#64]),
      Flapjack.WordLangExpHOL.const 136#64])

def sourceBody622_201 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 6331469388073975673#64)

def sourceBody622_202 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_201 sourceBody622_82

def sourceBody622_203 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_10 sourceBody622_202

def sourceBody622_204 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_200 sourceBody622_203

def sourceBody622_205 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_10 sourceBody622_204

def sourceBody622_206 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_199 sourceBody622_205

def sourceBody622_207 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 320#64]),
      Flapjack.WordLangExpHOL.const 144#64])

def sourceBody622_208 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 10330303817214507103#64)

def sourceBody622_209 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_208 sourceBody622_82

def sourceBody622_210 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_10 sourceBody622_209

def sourceBody622_211 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_207 sourceBody622_210

def sourceBody622_212 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_10 sourceBody622_211

def sourceBody622_213 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_206 sourceBody622_212

def sourceBody622_214 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 320#64]),
      Flapjack.WordLangExpHOL.const 152#64])

def sourceBody622_215 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 13537634492463488088#64)

def sourceBody622_216 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_215 sourceBody622_82

def sourceBody622_217 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_10 sourceBody622_216

def sourceBody622_218 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_214 sourceBody622_217

def sourceBody622_219 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_10 sourceBody622_218

def sourceBody622_220 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_213 sourceBody622_219

def sourceBody622_221 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody622_220 sourceBody622_12

def source622 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (622, 1, sourceBody622_221)
end InitECandidate.Proofs.WordStages
