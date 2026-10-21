import InitECandidate.Proofs.WordStages.Source369
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody385_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody385_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 2)

def sourceBody385_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 4)

def sourceBody385_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody385_4 : WordLangProgHOL (BitVec 64) :=
.call (some (([18, 8]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody385_0, 385, 2)) (some 186) ([16, 12]) (some (16, sourceBody385_3, 385, 3))

def sourceBody385_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody385_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_4 sourceBody385_5

def sourceBody385_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_6 sourceBody385_0

def sourceBody385_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_2 sourceBody385_7

def sourceBody385_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_1 sourceBody385_8

def sourceBody385_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 18)

def sourceBody385_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody385_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody385_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody385_14 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 12 (Flapjack.WordRegImm.reg 20) sourceBody385_12 sourceBody385_13

def sourceBody385_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_14 sourceBody385_5

def sourceBody385_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 12)

def sourceBody385_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody385_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [16]

def sourceBody385_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_18 sourceBody385_0

def sourceBody385_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_17 sourceBody385_19

def sourceBody385_21 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.WordRegImm.imm 0#64) sourceBody385_20 sourceBody385_0

def sourceBody385_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_21 sourceBody385_5

def sourceBody385_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_22 sourceBody385_0

def sourceBody385_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_16 sourceBody385_23

def sourceBody385_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_15 sourceBody385_24

def sourceBody385_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_11 sourceBody385_25

def sourceBody385_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_10 sourceBody385_26

def sourceBody385_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody385_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 208#64]))

def sourceBody385_30 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notLower) 12 (Flapjack.WordRegImm.reg 20) sourceBody385_12 sourceBody385_13

def sourceBody385_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_30 sourceBody385_5

def sourceBody385_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 5#64)

def sourceBody385_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody385_34 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody385_0, 385, 4)) (some 66) ([12]) (some (12, sourceBody385_33, 385, 5))

def sourceBody385_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_34 sourceBody385_5

def sourceBody385_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_35 sourceBody385_0

def sourceBody385_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_32 sourceBody385_36

def sourceBody385_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_0 sourceBody385_37

def sourceBody385_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_0 sourceBody385_38

def sourceBody385_40 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.WordRegImm.imm 0#64) sourceBody385_39 sourceBody385_0

def sourceBody385_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_40 sourceBody385_5

def sourceBody385_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_41 sourceBody385_0

def sourceBody385_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_16 sourceBody385_42

def sourceBody385_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_31 sourceBody385_43

def sourceBody385_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_29 sourceBody385_44

def sourceBody385_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_28 sourceBody385_45

def sourceBody385_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_27 sourceBody385_46

def sourceBody385_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 0#64]))

def sourceBody385_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 16)

def sourceBody385_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody385_51 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody385_0, 385, 6)) (some 68) ([20]) (some (20, sourceBody385_50, 385, 7))

def sourceBody385_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_51 sourceBody385_5

def sourceBody385_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_52 sourceBody385_0

def sourceBody385_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_49 sourceBody385_53

def sourceBody385_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 4)

def sourceBody385_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 16)

def sourceBody385_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody385_58 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody385_0, 385, 8)) (some 77) ([6, 14, 10]) (some (6, sourceBody385_57, 385, 9))

def sourceBody385_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_58 sourceBody385_5

def sourceBody385_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_59 sourceBody385_0

def sourceBody385_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_56 sourceBody385_60

def sourceBody385_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_55 sourceBody385_61

def sourceBody385_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_16 sourceBody385_62

def sourceBody385_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_0 sourceBody385_63

def sourceBody385_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_0 sourceBody385_64

def sourceBody385_66 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 200#64]),
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
        (Flapjack.WordLangExpHOL.load
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
            [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                  Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                    (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                    (Flapjack.WordLangExpHOL.const 1#64)],
              Flapjack.WordLangExpHOL.const 16#64]))
        (Flapjack.WordLangExpHOL.const 5#64)])

def sourceBody385_67 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 20)

def sourceBody385_68 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 2)

def sourceBody385_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 14)

def sourceBody385_70 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 6) 10

def sourceBody385_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_70 sourceBody385_0

def sourceBody385_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_69 sourceBody385_71

def sourceBody385_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_72 sourceBody385_0

def sourceBody385_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_68 sourceBody385_73

def sourceBody385_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_0 sourceBody385_74

def sourceBody385_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_67 sourceBody385_75

def sourceBody385_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_0 sourceBody385_76

def sourceBody385_78 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 20, Flapjack.WordLangExpHOL.const 8#64])

def sourceBody385_79 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 12)

def sourceBody385_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_79 sourceBody385_73

def sourceBody385_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_0 sourceBody385_80

def sourceBody385_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_78 sourceBody385_81

def sourceBody385_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_0 sourceBody385_82

def sourceBody385_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_77 sourceBody385_83

def sourceBody385_85 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 20, Flapjack.WordLangExpHOL.const 16#64])

def sourceBody385_86 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody385_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_86 sourceBody385_73

def sourceBody385_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_0 sourceBody385_87

def sourceBody385_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_85 sourceBody385_88

def sourceBody385_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_0 sourceBody385_89

def sourceBody385_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_84 sourceBody385_90

def sourceBody385_92 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 20, Flapjack.WordLangExpHOL.const 24#64])

def sourceBody385_93 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 8)

def sourceBody385_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_93 sourceBody385_73

def sourceBody385_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_0 sourceBody385_94

def sourceBody385_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_92 sourceBody385_95

def sourceBody385_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_0 sourceBody385_96

def sourceBody385_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_91 sourceBody385_97

def sourceBody385_99 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
        [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
          Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
            (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
      Flapjack.WordLangExpHOL.const 16#64])

def sourceBody385_100 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 16#64]),
      Flapjack.WordLangExpHOL.const 1#64])

def sourceBody385_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_100 sourceBody385_73

def sourceBody385_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_0 sourceBody385_101

def sourceBody385_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_99 sourceBody385_102

def sourceBody385_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_0 sourceBody385_103

def sourceBody385_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_98 sourceBody385_104

def sourceBody385_106 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 4)

def sourceBody385_107 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody385_108 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody385_0, 385, 10)) (some 193) ([14, 10]) (some (14, sourceBody385_107, 385, 11))

def sourceBody385_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_108 sourceBody385_5

def sourceBody385_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_109 sourceBody385_0

def sourceBody385_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_106 sourceBody385_110

def sourceBody385_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_68 sourceBody385_111

def sourceBody385_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_0 sourceBody385_112

def sourceBody385_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_0 sourceBody385_113

def sourceBody385_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_105 sourceBody385_114

def sourceBody385_116 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody385_117 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [6]

def sourceBody385_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_117 sourceBody385_0

def sourceBody385_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_116 sourceBody385_118

def sourceBody385_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_115 sourceBody385_119

def sourceBody385_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_66 sourceBody385_120

def sourceBody385_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_0 sourceBody385_121

def sourceBody385_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_65 sourceBody385_122

def sourceBody385_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_54 sourceBody385_123

def sourceBody385_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_0 sourceBody385_124

def sourceBody385_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_0 sourceBody385_125

def sourceBody385_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_48 sourceBody385_126

def sourceBody385_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_0 sourceBody385_127

def sourceBody385_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_47 sourceBody385_128

def sourceBody385_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_9 sourceBody385_129

def sourceBody385_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_0 sourceBody385_130

def sourceBody385_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_0 sourceBody385_131

def sourceBody385_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_0 sourceBody385_132

def sourceBody385_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody385_0 sourceBody385_133

def source385 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (385, 3, sourceBody385_134)
end InitECandidate.Proofs.WordStages
