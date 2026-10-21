import InitECandidate.Proofs.WordStages.Source637
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody653_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 376#64]))

def sourceBody653_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody653_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody653_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody653_4 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.reg 2) sourceBody653_2 sourceBody653_3

def sourceBody653_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody653_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_4 sourceBody653_5

def sourceBody653_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 10)

def sourceBody653_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody653_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [4]

def sourceBody653_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody653_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_9 sourceBody653_10

def sourceBody653_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_8 sourceBody653_11

def sourceBody653_13 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.WordRegImm.imm 0#64) sourceBody653_12 sourceBody653_10

def sourceBody653_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_13 sourceBody653_5

def sourceBody653_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_14 sourceBody653_10

def sourceBody653_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_7 sourceBody653_15

def sourceBody653_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_6 sourceBody653_16

def sourceBody653_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_1 sourceBody653_17

def sourceBody653_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_0 sourceBody653_18

def sourceBody653_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 384#64)

def sourceBody653_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody653_22 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody653_10, 653, 2)) (some 68) ([10]) (some (10, sourceBody653_21, 653, 3))

def sourceBody653_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_22 sourceBody653_5

def sourceBody653_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_23 sourceBody653_10

def sourceBody653_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_20 sourceBody653_24

def sourceBody653_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
        [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
          Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
            (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
      Flapjack.WordLangExpHOL.const 376#64])

def sourceBody653_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 4)

def sourceBody653_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 2)

def sourceBody653_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 10) 8

def sourceBody653_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_29 sourceBody653_10

def sourceBody653_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_28 sourceBody653_30

def sourceBody653_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_31 sourceBody653_10

def sourceBody653_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_27 sourceBody653_32

def sourceBody653_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_33

def sourceBody653_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_26 sourceBody653_34

def sourceBody653_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_35

def sourceBody653_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_25 sourceBody653_36

def sourceBody653_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_37

def sourceBody653_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_38

def sourceBody653_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_19 sourceBody653_39

def sourceBody653_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 376#64]))

def sourceBody653_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 15230403791020821917#64)

def sourceBody653_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 754611498739239741#64)

def sourceBody653_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 7381016538464732716#64)

def sourceBody653_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 1011752739694698287#64)

def sourceBody653_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 10)

def sourceBody653_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 4) 12

def sourceBody653_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_47 sourceBody653_10

def sourceBody653_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_46 sourceBody653_48

def sourceBody653_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 2)

def sourceBody653_51 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 8#64]) 12

def sourceBody653_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_51 sourceBody653_10

def sourceBody653_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_50 sourceBody653_52

def sourceBody653_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 8)

def sourceBody653_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 16#64])
  12

def sourceBody653_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_55 sourceBody653_10

def sourceBody653_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_54 sourceBody653_56

def sourceBody653_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 6)

def sourceBody653_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 24#64])
  12

def sourceBody653_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_59 sourceBody653_10

def sourceBody653_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_58 sourceBody653_60

def sourceBody653_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_61 sourceBody653_10

def sourceBody653_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_57 sourceBody653_62

def sourceBody653_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_53 sourceBody653_63

def sourceBody653_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_49 sourceBody653_64

def sourceBody653_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_45 sourceBody653_65

def sourceBody653_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_66

def sourceBody653_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_44 sourceBody653_67

def sourceBody653_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_68

def sourceBody653_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_43 sourceBody653_69

def sourceBody653_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_70

def sourceBody653_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_42 sourceBody653_71

def sourceBody653_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_72

def sourceBody653_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_41 sourceBody653_73

def sourceBody653_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_74

def sourceBody653_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_40 sourceBody653_75

def sourceBody653_77 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 376#64]),
      Flapjack.WordLangExpHOL.const 32#64])

def sourceBody653_78 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody653_79 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody653_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_79 sourceBody653_65

def sourceBody653_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_80

def sourceBody653_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_78 sourceBody653_81

def sourceBody653_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_82

def sourceBody653_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_1 sourceBody653_83

def sourceBody653_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_84

def sourceBody653_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_3 sourceBody653_85

def sourceBody653_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_86

def sourceBody653_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_77 sourceBody653_87

def sourceBody653_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_88

def sourceBody653_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_76 sourceBody653_89

def sourceBody653_91 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 376#64]),
      Flapjack.WordLangExpHOL.const 64#64])

def sourceBody653_92 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 12653890742059813127#64)

def sourceBody653_93 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 14585784200204367754#64)

def sourceBody653_94 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 1278438861261381767#64)

def sourceBody653_95 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 212598772761311868#64)

def sourceBody653_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_95 sourceBody653_65

def sourceBody653_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_96

def sourceBody653_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_94 sourceBody653_97

def sourceBody653_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_98

def sourceBody653_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_93 sourceBody653_99

def sourceBody653_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_100

def sourceBody653_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_92 sourceBody653_101

def sourceBody653_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_102

def sourceBody653_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_91 sourceBody653_103

def sourceBody653_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_104

def sourceBody653_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_90 sourceBody653_105

def sourceBody653_107 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 376#64]),
      Flapjack.WordLangExpHOL.const 96#64])

def sourceBody653_108 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 11683091849979440498#64)

def sourceBody653_109 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 14992204589386555739#64)

def sourceBody653_110 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 15866167890766973222#64)

def sourceBody653_111 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 1200023580730561873#64)

def sourceBody653_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_111 sourceBody653_65

def sourceBody653_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_112

def sourceBody653_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_110 sourceBody653_113

def sourceBody653_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_114

def sourceBody653_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_109 sourceBody653_115

def sourceBody653_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_116

def sourceBody653_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_108 sourceBody653_117

def sourceBody653_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_118

def sourceBody653_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_107 sourceBody653_119

def sourceBody653_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_120

def sourceBody653_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_106 sourceBody653_121

def sourceBody653_123 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 376#64]),
      Flapjack.WordLangExpHOL.const 128#64])

def sourceBody653_124 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 13075984984163199792#64)

def sourceBody653_125 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 3782902503040509012#64)

def sourceBody653_126 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 8791150885551868305#64)

def sourceBody653_127 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 1825854335138010348#64)

def sourceBody653_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_127 sourceBody653_65

def sourceBody653_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_128

def sourceBody653_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_126 sourceBody653_129

def sourceBody653_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_130

def sourceBody653_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_125 sourceBody653_131

def sourceBody653_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_132

def sourceBody653_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_124 sourceBody653_133

def sourceBody653_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_134

def sourceBody653_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_123 sourceBody653_135

def sourceBody653_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_136

def sourceBody653_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_122 sourceBody653_137

def sourceBody653_139 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 376#64]),
      Flapjack.WordLangExpHOL.const 160#64])

def sourceBody653_140 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 7963664994991228759#64)

def sourceBody653_141 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 12257807996192067905#64)

def sourceBody653_142 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 13179524609921305146#64)

def sourceBody653_143 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 2767831111890561987#64)

def sourceBody653_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_143 sourceBody653_65

def sourceBody653_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_144

def sourceBody653_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_142 sourceBody653_145

def sourceBody653_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_146

def sourceBody653_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_141 sourceBody653_147

def sourceBody653_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_148

def sourceBody653_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_140 sourceBody653_149

def sourceBody653_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_150

def sourceBody653_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_139 sourceBody653_151

def sourceBody653_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_152

def sourceBody653_154 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_138 sourceBody653_153

def sourceBody653_155 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 376#64]),
      Flapjack.WordLangExpHOL.const 192#64])

def sourceBody653_156 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 16482010305593259561#64)

def sourceBody653_157 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 13488546290961988299#64)

def sourceBody653_158 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 3578621962720924518#64)

def sourceBody653_159 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 2681173117283399901#64)

def sourceBody653_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_159 sourceBody653_65

def sourceBody653_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_160

def sourceBody653_162 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_158 sourceBody653_161

def sourceBody653_163 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_162

def sourceBody653_164 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_157 sourceBody653_163

def sourceBody653_165 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_164

def sourceBody653_166 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_156 sourceBody653_165

def sourceBody653_167 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_166

def sourceBody653_168 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_155 sourceBody653_167

def sourceBody653_169 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_168

def sourceBody653_170 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_154 sourceBody653_169

def sourceBody653_171 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 376#64]),
      Flapjack.WordLangExpHOL.const 224#64])

def sourceBody653_172 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 11661927080404088775#64)

def sourceBody653_173 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 553939530661941723#64)

def sourceBody653_174 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 7860678177968807019#64)

def sourceBody653_175 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 3208568454732775116#64)

def sourceBody653_176 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_175 sourceBody653_65

def sourceBody653_177 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_176

def sourceBody653_178 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_174 sourceBody653_177

def sourceBody653_179 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_178

def sourceBody653_180 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_173 sourceBody653_179

def sourceBody653_181 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_180

def sourceBody653_182 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_172 sourceBody653_181

def sourceBody653_183 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_182

def sourceBody653_184 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_171 sourceBody653_183

def sourceBody653_185 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_184

def sourceBody653_186 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_170 sourceBody653_185

def sourceBody653_187 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 376#64]),
      Flapjack.WordLangExpHOL.const 256#64])

def sourceBody653_188 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 8314163329781907090#64)

def sourceBody653_189 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 11942187022798819835#64)

def sourceBody653_190 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 11282677263046157209#64)

def sourceBody653_191 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 1576150870752482284#64)

def sourceBody653_192 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_191 sourceBody653_65

def sourceBody653_193 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_192

def sourceBody653_194 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_190 sourceBody653_193

def sourceBody653_195 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_194

def sourceBody653_196 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_189 sourceBody653_195

def sourceBody653_197 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_196

def sourceBody653_198 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_188 sourceBody653_197

def sourceBody653_199 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_198

def sourceBody653_200 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_187 sourceBody653_199

def sourceBody653_201 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_200

def sourceBody653_202 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_186 sourceBody653_201

def sourceBody653_203 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 376#64]),
      Flapjack.WordLangExpHOL.const 288#64])

def sourceBody653_204 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 6763840483288992073#64)

def sourceBody653_205 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 7118829427391486816#64)

def sourceBody653_206 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 4016233444936635065#64)

def sourceBody653_207 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 2630958277570195709#64)

def sourceBody653_208 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_207 sourceBody653_65

def sourceBody653_209 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_208

def sourceBody653_210 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_206 sourceBody653_209

def sourceBody653_211 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_210

def sourceBody653_212 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_205 sourceBody653_211

def sourceBody653_213 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_212

def sourceBody653_214 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_204 sourceBody653_213

def sourceBody653_215 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_214

def sourceBody653_216 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_203 sourceBody653_215

def sourceBody653_217 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_216

def sourceBody653_218 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_202 sourceBody653_217

def sourceBody653_219 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 376#64]),
      Flapjack.WordLangExpHOL.const 320#64])

def sourceBody653_220 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 14515217250696892391#64)

def sourceBody653_221 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 16303087968080972555#64)

def sourceBody653_222 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 3656613296917993960#64)

def sourceBody653_223 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 1345095164996126785#64)

def sourceBody653_224 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_223 sourceBody653_65

def sourceBody653_225 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_224

def sourceBody653_226 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_222 sourceBody653_225

def sourceBody653_227 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_226

def sourceBody653_228 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_221 sourceBody653_227

def sourceBody653_229 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_228

def sourceBody653_230 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_220 sourceBody653_229

def sourceBody653_231 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_230

def sourceBody653_232 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_219 sourceBody653_231

def sourceBody653_233 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_232

def sourceBody653_234 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_218 sourceBody653_233

def sourceBody653_235 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 376#64]),
      Flapjack.WordLangExpHOL.const 352#64])

def sourceBody653_236 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 957117326806663081#64)

def sourceBody653_237 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 367382125163301975#64)

def sourceBody653_238 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 15253872307375509749#64)

def sourceBody653_239 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 3396254757538665050#64)

def sourceBody653_240 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_239 sourceBody653_65

def sourceBody653_241 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_240

def sourceBody653_242 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_238 sourceBody653_241

def sourceBody653_243 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_242

def sourceBody653_244 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_237 sourceBody653_243

def sourceBody653_245 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_244

def sourceBody653_246 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_236 sourceBody653_245

def sourceBody653_247 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_246

def sourceBody653_248 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_235 sourceBody653_247

def sourceBody653_249 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_248

def sourceBody653_250 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_234 sourceBody653_249

def sourceBody653_251 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 352#64)

def sourceBody653_252 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody653_10, 653, 4)) (some 68) ([10]) (some (10, sourceBody653_21, 653, 5))

def sourceBody653_253 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_252 sourceBody653_5

def sourceBody653_254 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_253 sourceBody653_10

def sourceBody653_255 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_251 sourceBody653_254

def sourceBody653_256 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
        [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
          Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
            (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
      Flapjack.WordLangExpHOL.const 384#64])

def sourceBody653_257 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_256 sourceBody653_34

def sourceBody653_258 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_257

def sourceBody653_259 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_255 sourceBody653_258

def sourceBody653_260 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_259

def sourceBody653_261 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_260

def sourceBody653_262 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_250 sourceBody653_261

def sourceBody653_263 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 384#64]))

def sourceBody653_264 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 9698021743855595808#64)

def sourceBody653_265 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 10)

def sourceBody653_266 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 4) 2

def sourceBody653_267 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_266 sourceBody653_10

def sourceBody653_268 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_265 sourceBody653_267

def sourceBody653_269 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_268 sourceBody653_10

def sourceBody653_270 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_264 sourceBody653_269

def sourceBody653_271 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_270

def sourceBody653_272 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_263 sourceBody653_271

def sourceBody653_273 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_272

def sourceBody653_274 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_262 sourceBody653_273

def sourceBody653_275 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 384#64]),
      Flapjack.WordLangExpHOL.const 8#64])

def sourceBody653_276 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 4658111487712502692#64)

def sourceBody653_277 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_276 sourceBody653_269

def sourceBody653_278 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_277

def sourceBody653_279 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_275 sourceBody653_278

def sourceBody653_280 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_279

def sourceBody653_281 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_274 sourceBody653_280

def sourceBody653_282 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 384#64]),
      Flapjack.WordLangExpHOL.const 16#64])

def sourceBody653_283 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 9475478476403788475#64)

def sourceBody653_284 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_283 sourceBody653_269

def sourceBody653_285 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_284

def sourceBody653_286 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_282 sourceBody653_285

def sourceBody653_287 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_286

def sourceBody653_288 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_281 sourceBody653_287

def sourceBody653_289 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 384#64]),
      Flapjack.WordLangExpHOL.const 24#64])

def sourceBody653_290 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 3895898136474990872#64)

def sourceBody653_291 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_290 sourceBody653_269

def sourceBody653_292 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_291

def sourceBody653_293 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_289 sourceBody653_292

def sourceBody653_294 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_293

def sourceBody653_295 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_288 sourceBody653_294

def sourceBody653_296 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 384#64]),
      Flapjack.WordLangExpHOL.const 32#64])

def sourceBody653_297 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 13897688294677189338#64)

def sourceBody653_298 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_297 sourceBody653_269

def sourceBody653_299 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_298

def sourceBody653_300 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_296 sourceBody653_299

def sourceBody653_301 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_300

def sourceBody653_302 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_295 sourceBody653_301

def sourceBody653_303 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 384#64]),
      Flapjack.WordLangExpHOL.const 40#64])

def sourceBody653_304 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 13692288569157338976#64)

def sourceBody653_305 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_304 sourceBody653_269

def sourceBody653_306 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_305

def sourceBody653_307 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_303 sourceBody653_306

def sourceBody653_308 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_307

def sourceBody653_309 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_302 sourceBody653_308

def sourceBody653_310 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 384#64]),
      Flapjack.WordLangExpHOL.const 48#64])

def sourceBody653_311 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 15521367811043670911#64)

def sourceBody653_312 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_311 sourceBody653_269

def sourceBody653_313 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_312

def sourceBody653_314 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_310 sourceBody653_313

def sourceBody653_315 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_314

def sourceBody653_316 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_309 sourceBody653_315

def sourceBody653_317 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 384#64]),
      Flapjack.WordLangExpHOL.const 56#64])

def sourceBody653_318 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 13992850401411864641#64)

def sourceBody653_319 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_318 sourceBody653_269

def sourceBody653_320 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_319

def sourceBody653_321 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_317 sourceBody653_320

def sourceBody653_322 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_321

def sourceBody653_323 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_316 sourceBody653_322

def sourceBody653_324 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 384#64]),
      Flapjack.WordLangExpHOL.const 64#64])

def sourceBody653_325 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 6609620042336070051#64)

def sourceBody653_326 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_325 sourceBody653_269

def sourceBody653_327 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_326

def sourceBody653_328 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_324 sourceBody653_327

def sourceBody653_329 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_328

def sourceBody653_330 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_323 sourceBody653_329

def sourceBody653_331 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 384#64]),
      Flapjack.WordLangExpHOL.const 72#64])

def sourceBody653_332 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 9167096575297741460#64)

def sourceBody653_333 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_332 sourceBody653_269

def sourceBody653_334 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_333

def sourceBody653_335 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_331 sourceBody653_334

def sourceBody653_336 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_335

def sourceBody653_337 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_330 sourceBody653_336

def sourceBody653_338 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 384#64]),
      Flapjack.WordLangExpHOL.const 80#64])

def sourceBody653_339 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 3006977925533509404#64)

def sourceBody653_340 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_339 sourceBody653_269

def sourceBody653_341 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_340

def sourceBody653_342 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_338 sourceBody653_341

def sourceBody653_343 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_342

def sourceBody653_344 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_337 sourceBody653_343

def sourceBody653_345 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 384#64]),
      Flapjack.WordLangExpHOL.const 88#64])

def sourceBody653_346 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 13799376210358020352#64)

def sourceBody653_347 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_346 sourceBody653_269

def sourceBody653_348 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_347

def sourceBody653_349 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_345 sourceBody653_348

def sourceBody653_350 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_349

def sourceBody653_351 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_344 sourceBody653_350

def sourceBody653_352 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 384#64]),
      Flapjack.WordLangExpHOL.const 96#64])

def sourceBody653_353 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 7213564696215919148#64)

def sourceBody653_354 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_353 sourceBody653_269

def sourceBody653_355 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_354

def sourceBody653_356 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_352 sourceBody653_355

def sourceBody653_357 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_356

def sourceBody653_358 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_351 sourceBody653_357

def sourceBody653_359 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 384#64]),
      Flapjack.WordLangExpHOL.const 104#64])

def sourceBody653_360 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 12108970941387295838#64)

def sourceBody653_361 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_360 sourceBody653_269

def sourceBody653_362 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_361

def sourceBody653_363 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_359 sourceBody653_362

def sourceBody653_364 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_363

def sourceBody653_365 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_358 sourceBody653_364

def sourceBody653_366 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 384#64]),
      Flapjack.WordLangExpHOL.const 112#64])

def sourceBody653_367 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 14800348210198864764#64)

def sourceBody653_368 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_367 sourceBody653_269

def sourceBody653_369 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_368

def sourceBody653_370 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_366 sourceBody653_369

def sourceBody653_371 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_370

def sourceBody653_372 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_365 sourceBody653_371

def sourceBody653_373 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 384#64]),
      Flapjack.WordLangExpHOL.const 120#64])

def sourceBody653_374 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 5333217130945090002#64)

def sourceBody653_375 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_374 sourceBody653_269

def sourceBody653_376 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_375

def sourceBody653_377 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_373 sourceBody653_376

def sourceBody653_378 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_377

def sourceBody653_379 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_372 sourceBody653_378

def sourceBody653_380 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 384#64]),
      Flapjack.WordLangExpHOL.const 128#64])

def sourceBody653_381 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 17191330154042290397#64)

def sourceBody653_382 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_381 sourceBody653_269

def sourceBody653_383 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_382

def sourceBody653_384 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_380 sourceBody653_383

def sourceBody653_385 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_384

def sourceBody653_386 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_379 sourceBody653_385

def sourceBody653_387 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 384#64]),
      Flapjack.WordLangExpHOL.const 136#64])

def sourceBody653_388 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 7728981312468502308#64)

def sourceBody653_389 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_388 sourceBody653_269

def sourceBody653_390 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_389

def sourceBody653_391 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_387 sourceBody653_390

def sourceBody653_392 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_391

def sourceBody653_393 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_386 sourceBody653_392

def sourceBody653_394 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 384#64]),
      Flapjack.WordLangExpHOL.const 144#64])

def sourceBody653_395 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 13479501571575199621#64)

def sourceBody653_396 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_395 sourceBody653_269

def sourceBody653_397 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_396

def sourceBody653_398 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_394 sourceBody653_397

def sourceBody653_399 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_398

def sourceBody653_400 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_393 sourceBody653_399

def sourceBody653_401 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 384#64]),
      Flapjack.WordLangExpHOL.const 152#64])

def sourceBody653_402 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 4632319730382815766#64)

def sourceBody653_403 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_402 sourceBody653_269

def sourceBody653_404 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_403

def sourceBody653_405 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_401 sourceBody653_404

def sourceBody653_406 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_405

def sourceBody653_407 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_400 sourceBody653_406

def sourceBody653_408 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 384#64]),
      Flapjack.WordLangExpHOL.const 160#64])

def sourceBody653_409 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 6183408236485651195#64)

def sourceBody653_410 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_409 sourceBody653_269

def sourceBody653_411 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_410

def sourceBody653_412 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_408 sourceBody653_411

def sourceBody653_413 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_412

def sourceBody653_414 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_407 sourceBody653_413

def sourceBody653_415 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 384#64]),
      Flapjack.WordLangExpHOL.const 168#64])

def sourceBody653_416 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 2344383644319854215#64)

def sourceBody653_417 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_416 sourceBody653_269

def sourceBody653_418 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_417

def sourceBody653_419 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_415 sourceBody653_418

def sourceBody653_420 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_419

def sourceBody653_421 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_414 sourceBody653_420

def sourceBody653_422 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 384#64]),
      Flapjack.WordLangExpHOL.const 176#64])

def sourceBody653_423 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 9541507823907846048#64)

def sourceBody653_424 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_423 sourceBody653_269

def sourceBody653_425 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_424

def sourceBody653_426 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_422 sourceBody653_425

def sourceBody653_427 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_426

def sourceBody653_428 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_421 sourceBody653_427

def sourceBody653_429 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 384#64]),
      Flapjack.WordLangExpHOL.const 184#64])

def sourceBody653_430 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 5234407941292577173#64)

def sourceBody653_431 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_430 sourceBody653_269

def sourceBody653_432 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_431

def sourceBody653_433 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_429 sourceBody653_432

def sourceBody653_434 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_433

def sourceBody653_435 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_428 sourceBody653_434

def sourceBody653_436 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 384#64]),
      Flapjack.WordLangExpHOL.const 192#64])

def sourceBody653_437 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 16529975799043132950#64)

def sourceBody653_438 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_437 sourceBody653_269

def sourceBody653_439 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_438

def sourceBody653_440 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_436 sourceBody653_439

def sourceBody653_441 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_440

def sourceBody653_442 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_435 sourceBody653_441

def sourceBody653_443 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 384#64]),
      Flapjack.WordLangExpHOL.const 200#64])

def sourceBody653_444 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 12351756573642376427#64)

def sourceBody653_445 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_444 sourceBody653_269

def sourceBody653_446 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_445

def sourceBody653_447 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_443 sourceBody653_446

def sourceBody653_448 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_447

def sourceBody653_449 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_442 sourceBody653_448

def sourceBody653_450 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 384#64]),
      Flapjack.WordLangExpHOL.const 208#64])

def sourceBody653_451 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 9426269327694809050#64)

def sourceBody653_452 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_451 sourceBody653_269

def sourceBody653_453 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_452

def sourceBody653_454 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_450 sourceBody653_453

def sourceBody653_455 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_454

def sourceBody653_456 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_449 sourceBody653_455

def sourceBody653_457 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 384#64]),
      Flapjack.WordLangExpHOL.const 216#64])

def sourceBody653_458 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 7379223421642392714#64)

def sourceBody653_459 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_458 sourceBody653_269

def sourceBody653_460 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_459

def sourceBody653_461 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_457 sourceBody653_460

def sourceBody653_462 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_461

def sourceBody653_463 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_456 sourceBody653_462

def sourceBody653_464 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 384#64]),
      Flapjack.WordLangExpHOL.const 224#64])

def sourceBody653_465 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 5792417538046516732#64)

def sourceBody653_466 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_465 sourceBody653_269

def sourceBody653_467 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_466

def sourceBody653_468 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_464 sourceBody653_467

def sourceBody653_469 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_468

def sourceBody653_470 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_463 sourceBody653_469

def sourceBody653_471 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 384#64]),
      Flapjack.WordLangExpHOL.const 232#64])

def sourceBody653_472 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 9162926010144764881#64)

def sourceBody653_473 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_472 sourceBody653_269

def sourceBody653_474 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_473

def sourceBody653_475 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_471 sourceBody653_474

def sourceBody653_476 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_475

def sourceBody653_477 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_470 sourceBody653_476

def sourceBody653_478 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 384#64]),
      Flapjack.WordLangExpHOL.const 240#64])

def sourceBody653_479 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 8644015420738790472#64)

def sourceBody653_480 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_479 sourceBody653_269

def sourceBody653_481 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_480

def sourceBody653_482 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_478 sourceBody653_481

def sourceBody653_483 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_482

def sourceBody653_484 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_477 sourceBody653_483

def sourceBody653_485 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 384#64]),
      Flapjack.WordLangExpHOL.const 248#64])

def sourceBody653_486 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 18370314904686314414#64)

def sourceBody653_487 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_486 sourceBody653_269

def sourceBody653_488 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_487

def sourceBody653_489 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_485 sourceBody653_488

def sourceBody653_490 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_489

def sourceBody653_491 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_484 sourceBody653_490

def sourceBody653_492 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 384#64]),
      Flapjack.WordLangExpHOL.const 256#64])

def sourceBody653_493 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 17975984934167627464#64)

def sourceBody653_494 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_493 sourceBody653_269

def sourceBody653_495 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_494

def sourceBody653_496 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_492 sourceBody653_495

def sourceBody653_497 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_496

def sourceBody653_498 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_491 sourceBody653_497

def sourceBody653_499 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 384#64]),
      Flapjack.WordLangExpHOL.const 264#64])

def sourceBody653_500 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 8719923968173632426#64)

def sourceBody653_501 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_500 sourceBody653_269

def sourceBody653_502 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_501

def sourceBody653_503 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_499 sourceBody653_502

def sourceBody653_504 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_503

def sourceBody653_505 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_498 sourceBody653_504

def sourceBody653_506 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 384#64]),
      Flapjack.WordLangExpHOL.const 272#64])

def sourceBody653_507 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 6379321585415610019#64)

def sourceBody653_508 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_507 sourceBody653_269

def sourceBody653_509 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_508

def sourceBody653_510 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_506 sourceBody653_509

def sourceBody653_511 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_510

def sourceBody653_512 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_505 sourceBody653_511

def sourceBody653_513 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 384#64]),
      Flapjack.WordLangExpHOL.const 280#64])

def sourceBody653_514 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 1402842025008175984#64)

def sourceBody653_515 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_514 sourceBody653_269

def sourceBody653_516 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_515

def sourceBody653_517 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_513 sourceBody653_516

def sourceBody653_518 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_517

def sourceBody653_519 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_512 sourceBody653_518

def sourceBody653_520 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 384#64]),
      Flapjack.WordLangExpHOL.const 288#64])

def sourceBody653_521 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 888598832447275954#64)

def sourceBody653_522 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_521 sourceBody653_269

def sourceBody653_523 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_522

def sourceBody653_524 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_520 sourceBody653_523

def sourceBody653_525 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_524

def sourceBody653_526 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_519 sourceBody653_525

def sourceBody653_527 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 384#64]),
      Flapjack.WordLangExpHOL.const 296#64])

def sourceBody653_528 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 4522688638863333623#64)

def sourceBody653_529 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_528 sourceBody653_269

def sourceBody653_530 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_529

def sourceBody653_531 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_527 sourceBody653_530

def sourceBody653_532 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_531

def sourceBody653_533 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_526 sourceBody653_532

def sourceBody653_534 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 384#64]),
      Flapjack.WordLangExpHOL.const 304#64])

def sourceBody653_535 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 15776483769708984925#64)

def sourceBody653_536 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_535 sourceBody653_269

def sourceBody653_537 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_536

def sourceBody653_538 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_534 sourceBody653_537

def sourceBody653_539 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_538

def sourceBody653_540 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_533 sourceBody653_539

def sourceBody653_541 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 384#64]),
      Flapjack.WordLangExpHOL.const 312#64])

def sourceBody653_542 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 16276864970431725248#64)

def sourceBody653_543 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_542 sourceBody653_269

def sourceBody653_544 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_543

def sourceBody653_545 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_541 sourceBody653_544

def sourceBody653_546 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_545

def sourceBody653_547 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_540 sourceBody653_546

def sourceBody653_548 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 384#64]),
      Flapjack.WordLangExpHOL.const 320#64])

def sourceBody653_549 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 7646110518075161570#64)

def sourceBody653_550 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_549 sourceBody653_269

def sourceBody653_551 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_550

def sourceBody653_552 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_548 sourceBody653_551

def sourceBody653_553 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_552

def sourceBody653_554 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_547 sourceBody653_553

def sourceBody653_555 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 384#64]),
      Flapjack.WordLangExpHOL.const 328#64])

def sourceBody653_556 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 9524343276244152831#64)

def sourceBody653_557 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_556 sourceBody653_269

def sourceBody653_558 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_557

def sourceBody653_559 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_555 sourceBody653_558

def sourceBody653_560 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_559

def sourceBody653_561 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_554 sourceBody653_560

def sourceBody653_562 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 384#64]),
      Flapjack.WordLangExpHOL.const 336#64])

def sourceBody653_563 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 2377296829910687932#64)

def sourceBody653_564 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_563 sourceBody653_269

def sourceBody653_565 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_564

def sourceBody653_566 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_562 sourceBody653_565

def sourceBody653_567 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_566

def sourceBody653_568 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_561 sourceBody653_567

def sourceBody653_569 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 384#64]),
      Flapjack.WordLangExpHOL.const 344#64])

def sourceBody653_570 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 203128949104#64)

def sourceBody653_571 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_570 sourceBody653_269

def sourceBody653_572 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_571

def sourceBody653_573 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_569 sourceBody653_572

def sourceBody653_574 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_10 sourceBody653_573

def sourceBody653_575 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_568 sourceBody653_574

def sourceBody653_576 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody653_575 sourceBody653_12

def source653 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (653, 1, sourceBody653_576)
end InitECandidate.Proofs.WordStages
