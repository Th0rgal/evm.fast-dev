import InitECandidate.Proofs.WordStages.Source368
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody384_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody384_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 2)

def sourceBody384_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 4)

def sourceBody384_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody384_4 : WordLangProgHOL (BitVec 64) :=
.call (some (([10, 20]), ((Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody384_0, 384, 2)) (some 186) ([16, 24]) (some (16, sourceBody384_3, 384, 3))

def sourceBody384_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody384_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody384_4 sourceBody384_5

def sourceBody384_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody384_6 sourceBody384_0

def sourceBody384_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody384_2 sourceBody384_7

def sourceBody384_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody384_1 sourceBody384_8

def sourceBody384_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody384_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 208#64]))

def sourceBody384_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody384_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody384_14 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notLower) 24 (Flapjack.WordRegImm.reg 8) sourceBody384_12 sourceBody384_13

def sourceBody384_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody384_14 sourceBody384_5

def sourceBody384_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 24)

def sourceBody384_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 4#64)

def sourceBody384_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 24

def sourceBody384_19 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody384_0, 384, 4)) (some 66) ([24]) (some (24, sourceBody384_18, 384, 5))

def sourceBody384_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody384_19 sourceBody384_5

def sourceBody384_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody384_20 sourceBody384_0

def sourceBody384_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody384_17 sourceBody384_21

def sourceBody384_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody384_0 sourceBody384_22

def sourceBody384_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody384_0 sourceBody384_23

def sourceBody384_25 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 18 (Flapjack.WordRegImm.imm 0#64) sourceBody384_24 sourceBody384_0

def sourceBody384_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody384_25 sourceBody384_5

def sourceBody384_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody384_26 sourceBody384_0

def sourceBody384_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody384_16 sourceBody384_27

def sourceBody384_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody384_15 sourceBody384_28

def sourceBody384_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody384_11 sourceBody384_29

def sourceBody384_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody384_10 sourceBody384_30

def sourceBody384_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 0#64]))

def sourceBody384_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 16)

def sourceBody384_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody384_35 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody384_0, 384, 6)) (some 68) ([8]) (some (8, sourceBody384_34, 384, 7))

def sourceBody384_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody384_35 sourceBody384_5

def sourceBody384_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody384_36 sourceBody384_0

def sourceBody384_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody384_33 sourceBody384_37

def sourceBody384_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 4)

def sourceBody384_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 16)

def sourceBody384_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody384_42 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody384_0, 384, 8)) (some 77) ([18, 14, 22]) (some (18, sourceBody384_41, 384, 9))

def sourceBody384_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody384_42 sourceBody384_5

def sourceBody384_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody384_43 sourceBody384_0

def sourceBody384_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody384_40 sourceBody384_44

def sourceBody384_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody384_39 sourceBody384_45

def sourceBody384_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody384_16 sourceBody384_46

def sourceBody384_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody384_0 sourceBody384_47

def sourceBody384_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody384_0 sourceBody384_48

def sourceBody384_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
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

def sourceBody384_51 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 8)

def sourceBody384_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 2)

def sourceBody384_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 14)

def sourceBody384_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 18) 22

def sourceBody384_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody384_54 sourceBody384_0

def sourceBody384_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody384_53 sourceBody384_55

def sourceBody384_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody384_56 sourceBody384_0

def sourceBody384_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody384_52 sourceBody384_57

def sourceBody384_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody384_0 sourceBody384_58

def sourceBody384_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody384_51 sourceBody384_59

def sourceBody384_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody384_0 sourceBody384_60

def sourceBody384_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 8#64])

def sourceBody384_63 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 24)

def sourceBody384_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody384_63 sourceBody384_57

def sourceBody384_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody384_0 sourceBody384_64

def sourceBody384_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody384_62 sourceBody384_65

def sourceBody384_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody384_0 sourceBody384_66

def sourceBody384_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody384_61 sourceBody384_67

def sourceBody384_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 16#64])

def sourceBody384_70 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 10)

def sourceBody384_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody384_70 sourceBody384_57

def sourceBody384_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody384_0 sourceBody384_71

def sourceBody384_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody384_69 sourceBody384_72

def sourceBody384_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody384_0 sourceBody384_73

def sourceBody384_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody384_68 sourceBody384_74

def sourceBody384_76 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 24#64])

def sourceBody384_77 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 20)

def sourceBody384_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody384_77 sourceBody384_57

def sourceBody384_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody384_0 sourceBody384_78

def sourceBody384_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody384_76 sourceBody384_79

def sourceBody384_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody384_0 sourceBody384_80

def sourceBody384_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody384_75 sourceBody384_81

def sourceBody384_83 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
        [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
          Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
            (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
      Flapjack.WordLangExpHOL.const 16#64])

def sourceBody384_84 : WordLangProgHOL (BitVec 64) :=
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

def sourceBody384_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody384_84 sourceBody384_57

def sourceBody384_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody384_0 sourceBody384_85

def sourceBody384_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody384_83 sourceBody384_86

def sourceBody384_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody384_0 sourceBody384_87

def sourceBody384_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody384_82 sourceBody384_88

def sourceBody384_90 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 4)

def sourceBody384_91 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 6)

def sourceBody384_92 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody384_93 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody384_0, 384, 10)) (some 192) ([14, 22, 12]) (some (14, sourceBody384_92, 384, 11))

def sourceBody384_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody384_93 sourceBody384_5

def sourceBody384_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody384_94 sourceBody384_0

def sourceBody384_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody384_91 sourceBody384_95

def sourceBody384_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody384_90 sourceBody384_96

def sourceBody384_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody384_52 sourceBody384_97

def sourceBody384_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody384_0 sourceBody384_98

def sourceBody384_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody384_0 sourceBody384_99

def sourceBody384_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody384_89 sourceBody384_100

def sourceBody384_102 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody384_103 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [18]

def sourceBody384_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody384_103 sourceBody384_0

def sourceBody384_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody384_102 sourceBody384_104

def sourceBody384_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody384_101 sourceBody384_105

def sourceBody384_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody384_50 sourceBody384_106

def sourceBody384_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody384_0 sourceBody384_107

def sourceBody384_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody384_49 sourceBody384_108

def sourceBody384_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody384_38 sourceBody384_109

def sourceBody384_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody384_0 sourceBody384_110

def sourceBody384_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody384_0 sourceBody384_111

def sourceBody384_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody384_32 sourceBody384_112

def sourceBody384_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody384_0 sourceBody384_113

def sourceBody384_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody384_31 sourceBody384_114

def sourceBody384_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody384_9 sourceBody384_115

def sourceBody384_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody384_0 sourceBody384_116

def sourceBody384_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody384_0 sourceBody384_117

def sourceBody384_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody384_0 sourceBody384_118

def sourceBody384_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody384_0 sourceBody384_119

def source384 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (384, 4, sourceBody384_120)
end InitECandidate.Proofs.WordStages
