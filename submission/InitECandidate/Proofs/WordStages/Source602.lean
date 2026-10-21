import InitECandidate.Proofs.WordStages.Source586
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody602_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 1024#64)

def sourceBody602_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 128#64]))

def sourceBody602_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody602_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody602_4 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 20 (Flapjack.WordRegImm.reg 6) sourceBody602_2 sourceBody602_3

def sourceBody602_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody602_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_4 sourceBody602_5

def sourceBody602_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 20)

def sourceBody602_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody602_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 7#64)

def sourceBody602_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 10)

def sourceBody602_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_10 sourceBody602_8

def sourceBody602_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_11 sourceBody602_8

def sourceBody602_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_9 sourceBody602_12

def sourceBody602_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_8 sourceBody602_13

def sourceBody602_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 8#64)

def sourceBody602_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody602_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_15 sourceBody602_16

def sourceBody602_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_14 sourceBody602_17

def sourceBody602_19 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 18 (Flapjack.WordRegImm.imm 0#64) sourceBody602_18 sourceBody602_8

def sourceBody602_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_19 sourceBody602_5

def sourceBody602_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_20 sourceBody602_8

def sourceBody602_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_7 sourceBody602_21

def sourceBody602_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_6 sourceBody602_22

def sourceBody602_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_1 sourceBody602_23

def sourceBody602_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_0 sourceBody602_24

def sourceBody602_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 256#64]))

def sourceBody602_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 288#64]))

def sourceBody602_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 2)

def sourceBody602_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody602_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody602_31 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody602_8, 602, 2)) (some 592) ([18, 14]) (some (18, sourceBody602_30, 602, 3))

def sourceBody602_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_31 sourceBody602_5

def sourceBody602_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_32 sourceBody602_8

def sourceBody602_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_29 sourceBody602_33

def sourceBody602_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_28 sourceBody602_34

def sourceBody602_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 128#64]))

def sourceBody602_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody602_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody602_39 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 14 (Flapjack.WordRegImm.reg 24) sourceBody602_38 sourceBody602_29

def sourceBody602_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_39 sourceBody602_5

def sourceBody602_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 14)

def sourceBody602_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody602_43 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody602_8, 602, 4)) (some 386) ([]) (some (14, sourceBody602_42, 602, 5))

def sourceBody602_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_43 sourceBody602_5

def sourceBody602_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_44 sourceBody602_8

def sourceBody602_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 48#64]))

def sourceBody602_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody602_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.lookup (Flapjack.WordStore.temp 0#5))

def sourceBody602_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_48 sourceBody602_8

def sourceBody602_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_49 sourceBody602_8

def sourceBody602_51 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 24)

def sourceBody602_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody602_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody602_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody602_55 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 12 (Flapjack.WordRegImm.reg 22) sourceBody602_53 sourceBody602_54

def sourceBody602_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_55 sourceBody602_5

def sourceBody602_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 12)

def sourceBody602_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 208#64]))

def sourceBody602_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody602_60 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody602_8, 602, 7)) (some 76) ([12]) (some (12, sourceBody602_59, 602, 8))

def sourceBody602_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_60 sourceBody602_5

def sourceBody602_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_61 sourceBody602_8

def sourceBody602_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_58 sourceBody602_62

def sourceBody602_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_8 sourceBody602_63

def sourceBody602_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_8 sourceBody602_64

def sourceBody602_66 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 224#64]))

def sourceBody602_67 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody602_8, 602, 9)) (some 73) ([12]) (some (12, sourceBody602_59, 602, 10))

def sourceBody602_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_67 sourceBody602_5

def sourceBody602_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_68 sourceBody602_8

def sourceBody602_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_66 sourceBody602_69

def sourceBody602_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_8 sourceBody602_70

def sourceBody602_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_8 sourceBody602_71

def sourceBody602_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_65 sourceBody602_72

def sourceBody602_74 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
        [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
          Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
            (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
      Flapjack.WordLangExpHOL.const 256#64])

def sourceBody602_75 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 10)

def sourceBody602_76 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 12)

def sourceBody602_77 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 16) 22

def sourceBody602_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_77 sourceBody602_8

def sourceBody602_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_76 sourceBody602_78

def sourceBody602_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_79 sourceBody602_8

def sourceBody602_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_75 sourceBody602_80

def sourceBody602_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_8 sourceBody602_81

def sourceBody602_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_74 sourceBody602_82

def sourceBody602_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_8 sourceBody602_83

def sourceBody602_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_73 sourceBody602_84

def sourceBody602_86 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
        [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
          Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
            (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
      Flapjack.WordLangExpHOL.const 288#64])

def sourceBody602_87 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 20)

def sourceBody602_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_87 sourceBody602_80

def sourceBody602_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_8 sourceBody602_88

def sourceBody602_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_86 sourceBody602_89

def sourceBody602_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_8 sourceBody602_90

def sourceBody602_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_85 sourceBody602_91

def sourceBody602_93 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 24)

def sourceBody602_94 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 16)

def sourceBody602_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_94 sourceBody602_8

def sourceBody602_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_95 sourceBody602_8

def sourceBody602_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_93 sourceBody602_96

def sourceBody602_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_8 sourceBody602_97

def sourceBody602_99 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 8#64)

def sourceBody602_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_99 sourceBody602_47

def sourceBody602_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_98 sourceBody602_100

def sourceBody602_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_92 sourceBody602_101

def sourceBody602_103 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.WordRegImm.imm 0#64) sourceBody602_102 sourceBody602_8

def sourceBody602_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_103 sourceBody602_5

def sourceBody602_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_104 sourceBody602_8

def sourceBody602_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_57 sourceBody602_105

def sourceBody602_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_56 sourceBody602_106

def sourceBody602_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_52 sourceBody602_107

def sourceBody602_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_51 sourceBody602_108

def sourceBody602_110 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 18)

def sourceBody602_111 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody602_8, 602, 11)) (some 387) ([12]) (some (12, sourceBody602_59, 602, 12))

def sourceBody602_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_111 sourceBody602_5

def sourceBody602_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_112 sourceBody602_8

def sourceBody602_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_110 sourceBody602_113

def sourceBody602_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_8 sourceBody602_114

def sourceBody602_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_8 sourceBody602_115

def sourceBody602_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_109 sourceBody602_116

def sourceBody602_118 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 48#64])

def sourceBody602_119 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 14)

def sourceBody602_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_119 sourceBody602_80

def sourceBody602_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_8 sourceBody602_120

def sourceBody602_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_118 sourceBody602_121

def sourceBody602_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_8 sourceBody602_122

def sourceBody602_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_117 sourceBody602_123

def sourceBody602_125 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 256#64]),
      Flapjack.WordLangExpHOL.const 200#64])

def sourceBody602_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_54 sourceBody602_80

def sourceBody602_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_8 sourceBody602_126

def sourceBody602_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_125 sourceBody602_127

def sourceBody602_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_8 sourceBody602_128

def sourceBody602_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_124 sourceBody602_129

def sourceBody602_131 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody602_8, 602, 13)) (some 470) ([]) (some (12, sourceBody602_59, 602, 14))

def sourceBody602_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_131 sourceBody602_5

def sourceBody602_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_132 sourceBody602_8

def sourceBody602_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_8 sourceBody602_133

def sourceBody602_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_8 sourceBody602_134

def sourceBody602_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_130 sourceBody602_135

def sourceBody602_137 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody602_8, 602, 15)) (some 600) ([12]) (some (12, sourceBody602_59, 602, 16))

def sourceBody602_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_137 sourceBody602_5

def sourceBody602_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_138 sourceBody602_8

def sourceBody602_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_51 sourceBody602_139

def sourceBody602_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_8 sourceBody602_140

def sourceBody602_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_8 sourceBody602_141

def sourceBody602_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_136 sourceBody602_142

def sourceBody602_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_143 sourceBody602_84

def sourceBody602_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_144 sourceBody602_91

def sourceBody602_146 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 6)

def sourceBody602_147 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [16]

def sourceBody602_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_147 sourceBody602_8

def sourceBody602_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_146 sourceBody602_148

def sourceBody602_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_145 sourceBody602_149

def sourceBody602_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_50 sourceBody602_150

def sourceBody602_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_5 sourceBody602_151

def sourceBody602_153 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 16 (Flapjack.WordRegImm.imm 8#64) sourceBody602_47 sourceBody602_152

def sourceBody602_154 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_153 sourceBody602_5

def sourceBody602_155 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody602_8, 602, 6)) (some 601) ([]) (some (16, sourceBody602_154, 602, 17))

def sourceBody602_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_155 sourceBody602_5

def sourceBody602_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_156 sourceBody602_8

def sourceBody602_158 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_8 sourceBody602_157

def sourceBody602_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_8 sourceBody602_158

def sourceBody602_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_8 sourceBody602_159

def sourceBody602_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_8 sourceBody602_160

def sourceBody602_162 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_46 sourceBody602_161

def sourceBody602_163 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_8 sourceBody602_162

def sourceBody602_164 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_45 sourceBody602_163

def sourceBody602_165 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_8 sourceBody602_164

def sourceBody602_166 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_8 sourceBody602_165

def sourceBody602_167 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 4 (Flapjack.WordRegImm.imm 0#64) sourceBody602_166 sourceBody602_8

def sourceBody602_168 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_167 sourceBody602_5

def sourceBody602_169 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_168 sourceBody602_8

def sourceBody602_170 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_41 sourceBody602_169

def sourceBody602_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_40 sourceBody602_170

def sourceBody602_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_37 sourceBody602_171

def sourceBody602_173 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_36 sourceBody602_172

def sourceBody602_174 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody602_8, 602, 18)) (some 386) ([]) (some (14, sourceBody602_42, 602, 19))

def sourceBody602_175 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_174 sourceBody602_5

def sourceBody602_176 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_175 sourceBody602_8

def sourceBody602_177 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 288#64]),
      Flapjack.WordLangExpHOL.const 24#64])

def sourceBody602_178 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 18)

def sourceBody602_179 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 24)

def sourceBody602_180 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 14) 4

def sourceBody602_181 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_180 sourceBody602_8

def sourceBody602_182 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_179 sourceBody602_181

def sourceBody602_183 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_182 sourceBody602_8

def sourceBody602_184 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_178 sourceBody602_183

def sourceBody602_185 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_8 sourceBody602_184

def sourceBody602_186 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_177 sourceBody602_185

def sourceBody602_187 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_8 sourceBody602_186

def sourceBody602_188 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 24

def sourceBody602_189 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody602_8, 602, 20)) (some 595) ([]) (some (24, sourceBody602_188, 602, 21))

def sourceBody602_190 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_189 sourceBody602_5

def sourceBody602_191 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_190 sourceBody602_8

def sourceBody602_192 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_8 sourceBody602_191

def sourceBody602_193 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_8 sourceBody602_192

def sourceBody602_194 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_187 sourceBody602_193

def sourceBody602_195 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody602_8, 602, 22)) (some 598) ([]) (some (24, sourceBody602_188, 602, 23))

def sourceBody602_196 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_195 sourceBody602_5

def sourceBody602_197 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_196 sourceBody602_8

def sourceBody602_198 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_8 sourceBody602_197

def sourceBody602_199 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_8 sourceBody602_198

def sourceBody602_200 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_194 sourceBody602_199

def sourceBody602_201 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 6)

def sourceBody602_202 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [14]

def sourceBody602_203 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_202 sourceBody602_8

def sourceBody602_204 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_201 sourceBody602_203

def sourceBody602_205 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_200 sourceBody602_204

def sourceBody602_206 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_176 sourceBody602_205

def sourceBody602_207 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_8 sourceBody602_206

def sourceBody602_208 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_8 sourceBody602_207

def sourceBody602_209 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_173 sourceBody602_208

def sourceBody602_210 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_35 sourceBody602_209

def sourceBody602_211 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_8 sourceBody602_210

def sourceBody602_212 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_8 sourceBody602_211

def sourceBody602_213 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_27 sourceBody602_212

def sourceBody602_214 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_8 sourceBody602_213

def sourceBody602_215 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_26 sourceBody602_214

def sourceBody602_216 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_8 sourceBody602_215

def sourceBody602_217 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody602_25 sourceBody602_216

def source602 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (602, 2, sourceBody602_217)
end InitECandidate.Proofs.WordStages
