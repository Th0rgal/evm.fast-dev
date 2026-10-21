import InitECandidate.Proofs.WordStages.Source462
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody478_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 2)

def sourceBody478_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody478_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody478_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody478_4 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 16 (Flapjack.WordRegImm.reg 6) sourceBody478_2 sourceBody478_3

def sourceBody478_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody478_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody478_4 sourceBody478_5

def sourceBody478_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 16)

def sourceBody478_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody478_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [8]

def sourceBody478_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody478_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody478_9 sourceBody478_10

def sourceBody478_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody478_8 sourceBody478_11

def sourceBody478_13 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.WordRegImm.imm 0#64) sourceBody478_12 sourceBody478_10

def sourceBody478_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody478_13 sourceBody478_5

def sourceBody478_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody478_14 sourceBody478_10

def sourceBody478_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody478_7 sourceBody478_15

def sourceBody478_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody478_6 sourceBody478_16

def sourceBody478_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody478_1 sourceBody478_17

def sourceBody478_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody478_0 sourceBody478_18

def sourceBody478_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
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
        Flapjack.WordLangExpHOL.const 32#64]))

def sourceBody478_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
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
        Flapjack.WordLangExpHOL.const 40#64]))

def sourceBody478_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.var 2])

def sourceBody478_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 16)

def sourceBody478_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 6)

def sourceBody478_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody478_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody478_27 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 10 (Flapjack.WordRegImm.reg 18) sourceBody478_25 sourceBody478_26

def sourceBody478_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody478_27 sourceBody478_5

def sourceBody478_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 10)

def sourceBody478_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 16)
    (Flapjack.WordLangExpHOL.const 1#64))

def sourceBody478_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 14)

def sourceBody478_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 6)

def sourceBody478_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody478_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody478_35 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 18 (Flapjack.WordRegImm.reg 4) sourceBody478_33 sourceBody478_34

def sourceBody478_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody478_35 sourceBody478_5

def sourceBody478_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 18)

def sourceBody478_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 1024#64])

def sourceBody478_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody478_38 sourceBody478_10

def sourceBody478_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody478_39 sourceBody478_10

def sourceBody478_41 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.imm 0#64) sourceBody478_40 sourceBody478_10

def sourceBody478_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody478_41 sourceBody478_5

def sourceBody478_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody478_42 sourceBody478_10

def sourceBody478_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody478_37 sourceBody478_43

def sourceBody478_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody478_36 sourceBody478_44

def sourceBody478_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody478_32 sourceBody478_45

def sourceBody478_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody478_31 sourceBody478_46

def sourceBody478_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.var 16])

def sourceBody478_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody478_50 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody478_10, 478, 2)) (some 71) ([18]) (some (18, sourceBody478_49, 478, 3))

def sourceBody478_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody478_50 sourceBody478_5

def sourceBody478_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody478_51 sourceBody478_10

def sourceBody478_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody478_48 sourceBody478_52

def sourceBody478_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody478_10 sourceBody478_53

def sourceBody478_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody478_10 sourceBody478_54

def sourceBody478_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody478_47 sourceBody478_55

def sourceBody478_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.load
              (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
                [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                    [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                        (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                        (Flapjack.WordLangExpHOL.const 1#64)],
                  Flapjack.WordLangExpHOL.const 256#64]),
            Flapjack.WordLangExpHOL.const 24#64]),
      Flapjack.WordLangExpHOL.var 16])

def sourceBody478_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.var 16])

def sourceBody478_59 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody478_10, 478, 4)) (some 78) ([18, 4]) (some (18, sourceBody478_49, 478, 5))

def sourceBody478_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody478_59 sourceBody478_5

def sourceBody478_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody478_60 sourceBody478_10

def sourceBody478_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody478_58 sourceBody478_61

def sourceBody478_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody478_57 sourceBody478_62

def sourceBody478_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody478_10 sourceBody478_63

def sourceBody478_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody478_10 sourceBody478_64

def sourceBody478_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody478_56 sourceBody478_65

def sourceBody478_67 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 256#64]),
      Flapjack.WordLangExpHOL.const 40#64])

def sourceBody478_68 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 18)

def sourceBody478_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 10) 4

def sourceBody478_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody478_69 sourceBody478_10

def sourceBody478_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody478_68 sourceBody478_70

def sourceBody478_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody478_71 sourceBody478_10

def sourceBody478_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody478_31 sourceBody478_72

def sourceBody478_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody478_10 sourceBody478_73

def sourceBody478_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody478_67 sourceBody478_74

def sourceBody478_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody478_10 sourceBody478_75

def sourceBody478_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody478_66 sourceBody478_76

def sourceBody478_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody478_30 sourceBody478_77

def sourceBody478_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody478_10 sourceBody478_78

def sourceBody478_80 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 4 (Flapjack.WordRegImm.imm 0#64) sourceBody478_79 sourceBody478_10

def sourceBody478_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody478_80 sourceBody478_5

def sourceBody478_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody478_81 sourceBody478_10

def sourceBody478_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody478_29 sourceBody478_82

def sourceBody478_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody478_28 sourceBody478_83

def sourceBody478_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody478_24 sourceBody478_84

def sourceBody478_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody478_23 sourceBody478_85

def sourceBody478_87 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.load
              (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
                [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                    [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                        (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                        (Flapjack.WordLangExpHOL.const 1#64)],
                  Flapjack.WordLangExpHOL.const 256#64]),
            Flapjack.WordLangExpHOL.const 24#64]),
      Flapjack.WordLangExpHOL.var 8])

def sourceBody478_88 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 2)

def sourceBody478_89 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody478_90 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody478_10, 478, 6)) (some 78) ([10, 18]) (some (10, sourceBody478_89, 478, 7))

def sourceBody478_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody478_90 sourceBody478_5

def sourceBody478_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody478_91 sourceBody478_10

def sourceBody478_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody478_88 sourceBody478_92

def sourceBody478_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody478_87 sourceBody478_93

def sourceBody478_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody478_10 sourceBody478_94

def sourceBody478_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody478_10 sourceBody478_95

def sourceBody478_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody478_86 sourceBody478_96

def sourceBody478_98 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 256#64]),
      Flapjack.WordLangExpHOL.const 32#64])

def sourceBody478_99 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 6)

def sourceBody478_100 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 10)

def sourceBody478_101 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 14) 18

def sourceBody478_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody478_101 sourceBody478_10

def sourceBody478_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody478_100 sourceBody478_102

def sourceBody478_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody478_103 sourceBody478_10

def sourceBody478_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody478_99 sourceBody478_104

def sourceBody478_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody478_10 sourceBody478_105

def sourceBody478_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody478_98 sourceBody478_106

def sourceBody478_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody478_10 sourceBody478_107

def sourceBody478_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody478_97 sourceBody478_108

def sourceBody478_110 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody478_111 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [14]

def sourceBody478_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody478_111 sourceBody478_10

def sourceBody478_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody478_110 sourceBody478_112

def sourceBody478_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody478_109 sourceBody478_113

def sourceBody478_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody478_22 sourceBody478_114

def sourceBody478_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody478_10 sourceBody478_115

def sourceBody478_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody478_21 sourceBody478_116

def sourceBody478_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody478_10 sourceBody478_117

def sourceBody478_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody478_20 sourceBody478_118

def sourceBody478_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody478_10 sourceBody478_119

def sourceBody478_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody478_19 sourceBody478_120

def source478 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (478, 2, sourceBody478_121)
end InitECandidate.Proofs.WordStages
