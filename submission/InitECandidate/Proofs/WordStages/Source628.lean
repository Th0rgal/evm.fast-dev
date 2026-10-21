import InitECandidate.Proofs.WordStages.Source612
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody628_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 352#64]))

def sourceBody628_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody628_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody628_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody628_4 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.WordRegImm.reg 2) sourceBody628_2 sourceBody628_3

def sourceBody628_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody628_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_4 sourceBody628_5

def sourceBody628_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 8)

def sourceBody628_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody628_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [4]

def sourceBody628_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody628_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_9 sourceBody628_10

def sourceBody628_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_8 sourceBody628_11

def sourceBody628_13 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.WordRegImm.imm 0#64) sourceBody628_12 sourceBody628_10

def sourceBody628_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_13 sourceBody628_5

def sourceBody628_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_14 sourceBody628_10

def sourceBody628_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_7 sourceBody628_15

def sourceBody628_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_6 sourceBody628_16

def sourceBody628_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_1 sourceBody628_17

def sourceBody628_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_0 sourceBody628_18

def sourceBody628_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 80#64)

def sourceBody628_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody628_22 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody628_10, 628, 2)) (some 68) ([8]) (some (8, sourceBody628_21, 628, 3))

def sourceBody628_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_22 sourceBody628_5

def sourceBody628_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_23 sourceBody628_10

def sourceBody628_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_20 sourceBody628_24

def sourceBody628_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
        [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
          Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
            (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
      Flapjack.WordLangExpHOL.const 352#64])

def sourceBody628_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 4)

def sourceBody628_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 2)

def sourceBody628_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 8) 6

def sourceBody628_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_29 sourceBody628_10

def sourceBody628_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_28 sourceBody628_30

def sourceBody628_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_31 sourceBody628_10

def sourceBody628_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_27 sourceBody628_32

def sourceBody628_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_10 sourceBody628_33

def sourceBody628_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_26 sourceBody628_34

def sourceBody628_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_10 sourceBody628_35

def sourceBody628_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_25 sourceBody628_36

def sourceBody628_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_10 sourceBody628_37

def sourceBody628_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_10 sourceBody628_38

def sourceBody628_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_19 sourceBody628_39

def sourceBody628_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 64#64)

def sourceBody628_42 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody628_10, 628, 4)) (some 68) ([8]) (some (8, sourceBody628_21, 628, 5))

def sourceBody628_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_42 sourceBody628_5

def sourceBody628_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_43 sourceBody628_10

def sourceBody628_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_41 sourceBody628_44

def sourceBody628_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
        [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
          Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
            (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
      Flapjack.WordLangExpHOL.const 360#64])

def sourceBody628_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_46 sourceBody628_34

def sourceBody628_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_10 sourceBody628_47

def sourceBody628_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_45 sourceBody628_48

def sourceBody628_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_10 sourceBody628_49

def sourceBody628_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_10 sourceBody628_50

def sourceBody628_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_40 sourceBody628_51

def sourceBody628_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 128#64)

def sourceBody628_54 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody628_10, 628, 6)) (some 68) ([8]) (some (8, sourceBody628_21, 628, 7))

def sourceBody628_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_54 sourceBody628_5

def sourceBody628_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_55 sourceBody628_10

def sourceBody628_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_53 sourceBody628_56

def sourceBody628_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
        [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
          Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
            (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
      Flapjack.WordLangExpHOL.const 368#64])

def sourceBody628_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_58 sourceBody628_34

def sourceBody628_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_10 sourceBody628_59

def sourceBody628_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_57 sourceBody628_60

def sourceBody628_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_10 sourceBody628_61

def sourceBody628_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_10 sourceBody628_62

def sourceBody628_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_52 sourceBody628_63

def sourceBody628_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 352#64]),
      Flapjack.WordLangExpHOL.const 0#64])

def sourceBody628_66 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 18364758544493064720#64)

def sourceBody628_67 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 8)

def sourceBody628_68 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 4) 2

def sourceBody628_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_68 sourceBody628_10

def sourceBody628_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_67 sourceBody628_69

def sourceBody628_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_70 sourceBody628_10

def sourceBody628_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_66 sourceBody628_71

def sourceBody628_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_10 sourceBody628_72

def sourceBody628_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_65 sourceBody628_73

def sourceBody628_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_10 sourceBody628_74

def sourceBody628_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_64 sourceBody628_75

def sourceBody628_77 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 352#64]),
      Flapjack.WordLangExpHOL.const 8#64])

def sourceBody628_78 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 3853709921291437230#64)

def sourceBody628_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_78 sourceBody628_71

def sourceBody628_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_10 sourceBody628_79

def sourceBody628_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_77 sourceBody628_80

def sourceBody628_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_10 sourceBody628_81

def sourceBody628_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_76 sourceBody628_82

def sourceBody628_84 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 352#64]),
      Flapjack.WordLangExpHOL.const 16#64])

def sourceBody628_85 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 5266788149650328715#64)

def sourceBody628_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_85 sourceBody628_71

def sourceBody628_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_10 sourceBody628_86

def sourceBody628_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_84 sourceBody628_87

def sourceBody628_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_10 sourceBody628_88

def sourceBody628_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_83 sourceBody628_89

def sourceBody628_91 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 352#64]),
      Flapjack.WordLangExpHOL.const 24#64])

def sourceBody628_92 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 10305543691612001175#64)

def sourceBody628_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_92 sourceBody628_71

def sourceBody628_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_10 sourceBody628_93

def sourceBody628_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_91 sourceBody628_94

def sourceBody628_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_10 sourceBody628_95

def sourceBody628_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_90 sourceBody628_96

def sourceBody628_98 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 352#64]),
      Flapjack.WordLangExpHOL.const 32#64])

def sourceBody628_99 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 15242093322790139145#64)

def sourceBody628_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_99 sourceBody628_71

def sourceBody628_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_10 sourceBody628_100

def sourceBody628_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_98 sourceBody628_101

def sourceBody628_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_10 sourceBody628_102

def sourceBody628_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_97 sourceBody628_103

def sourceBody628_105 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 352#64]),
      Flapjack.WordLangExpHOL.const 40#64])

def sourceBody628_106 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 10515720223929181890#64)

def sourceBody628_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_106 sourceBody628_71

def sourceBody628_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_10 sourceBody628_107

def sourceBody628_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_105 sourceBody628_108

def sourceBody628_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_10 sourceBody628_109

def sourceBody628_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_104 sourceBody628_110

def sourceBody628_112 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 352#64]),
      Flapjack.WordLangExpHOL.const 48#64])

def sourceBody628_113 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 13270197634454188380#64)

def sourceBody628_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_113 sourceBody628_71

def sourceBody628_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_10 sourceBody628_114

def sourceBody628_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_112 sourceBody628_115

def sourceBody628_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_10 sourceBody628_116

def sourceBody628_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_111 sourceBody628_117

def sourceBody628_119 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 352#64]),
      Flapjack.WordLangExpHOL.const 56#64])

def sourceBody628_120 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 11702690517083809725#64)

def sourceBody628_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_120 sourceBody628_71

def sourceBody628_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_10 sourceBody628_121

def sourceBody628_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_119 sourceBody628_122

def sourceBody628_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_10 sourceBody628_123

def sourceBody628_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_118 sourceBody628_124

def sourceBody628_126 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 352#64]),
      Flapjack.WordLangExpHOL.const 64#64])

def sourceBody628_127 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 6503616966983130870#64)

def sourceBody628_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_127 sourceBody628_71

def sourceBody628_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_10 sourceBody628_128

def sourceBody628_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_126 sourceBody628_129

def sourceBody628_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_10 sourceBody628_130

def sourceBody628_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_125 sourceBody628_131

def sourceBody628_133 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 352#64]),
      Flapjack.WordLangExpHOL.const 72#64])

def sourceBody628_134 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 991893350865389610#64)

def sourceBody628_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_134 sourceBody628_71

def sourceBody628_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_10 sourceBody628_135

def sourceBody628_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_133 sourceBody628_136

def sourceBody628_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_10 sourceBody628_137

def sourceBody628_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_132 sourceBody628_138

def sourceBody628_140 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 360#64]),
      Flapjack.WordLangExpHOL.const 0#64])

def sourceBody628_141 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 7640891576956012808#64)

def sourceBody628_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_141 sourceBody628_71

def sourceBody628_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_10 sourceBody628_142

def sourceBody628_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_140 sourceBody628_143

def sourceBody628_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_10 sourceBody628_144

def sourceBody628_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_139 sourceBody628_145

def sourceBody628_147 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 360#64]),
      Flapjack.WordLangExpHOL.const 8#64])

def sourceBody628_148 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 13503953896175478587#64)

def sourceBody628_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_148 sourceBody628_71

def sourceBody628_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_10 sourceBody628_149

def sourceBody628_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_147 sourceBody628_150

def sourceBody628_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_10 sourceBody628_151

def sourceBody628_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_146 sourceBody628_152

def sourceBody628_154 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 360#64]),
      Flapjack.WordLangExpHOL.const 16#64])

def sourceBody628_155 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 4354685564936845355#64)

def sourceBody628_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_155 sourceBody628_71

def sourceBody628_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_10 sourceBody628_156

def sourceBody628_158 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_154 sourceBody628_157

def sourceBody628_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_10 sourceBody628_158

def sourceBody628_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_153 sourceBody628_159

def sourceBody628_161 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 360#64]),
      Flapjack.WordLangExpHOL.const 24#64])

def sourceBody628_162 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 11912009170470909681#64)

def sourceBody628_163 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_162 sourceBody628_71

def sourceBody628_164 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_10 sourceBody628_163

def sourceBody628_165 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_161 sourceBody628_164

def sourceBody628_166 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_10 sourceBody628_165

def sourceBody628_167 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_160 sourceBody628_166

def sourceBody628_168 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 360#64]),
      Flapjack.WordLangExpHOL.const 32#64])

def sourceBody628_169 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 5840696475078001361#64)

def sourceBody628_170 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_169 sourceBody628_71

def sourceBody628_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_10 sourceBody628_170

def sourceBody628_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_168 sourceBody628_171

def sourceBody628_173 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_10 sourceBody628_172

def sourceBody628_174 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_167 sourceBody628_173

def sourceBody628_175 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 360#64]),
      Flapjack.WordLangExpHOL.const 40#64])

def sourceBody628_176 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 11170449401992604703#64)

def sourceBody628_177 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_176 sourceBody628_71

def sourceBody628_178 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_10 sourceBody628_177

def sourceBody628_179 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_175 sourceBody628_178

def sourceBody628_180 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_10 sourceBody628_179

def sourceBody628_181 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_174 sourceBody628_180

def sourceBody628_182 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 360#64]),
      Flapjack.WordLangExpHOL.const 48#64])

def sourceBody628_183 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 2270897969802886507#64)

def sourceBody628_184 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_183 sourceBody628_71

def sourceBody628_185 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_10 sourceBody628_184

def sourceBody628_186 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_182 sourceBody628_185

def sourceBody628_187 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_10 sourceBody628_186

def sourceBody628_188 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_181 sourceBody628_187

def sourceBody628_189 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 360#64]),
      Flapjack.WordLangExpHOL.const 56#64])

def sourceBody628_190 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 6620516959819538809#64)

def sourceBody628_191 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_190 sourceBody628_71

def sourceBody628_192 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_10 sourceBody628_191

def sourceBody628_193 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_189 sourceBody628_192

def sourceBody628_194 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_10 sourceBody628_193

def sourceBody628_195 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_188 sourceBody628_194

def sourceBody628_196 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody628_195 sourceBody628_12

def source628 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (628, 1, sourceBody628_196)
end InitECandidate.Proofs.WordStages
