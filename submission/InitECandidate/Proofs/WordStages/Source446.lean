import InitECandidate.Proofs.WordStages.Source430
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody446_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody446_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 248#64]))

def sourceBody446_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 26)

def sourceBody446_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 224#64]))

def sourceBody446_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 22

def sourceBody446_5 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody446_0, 446, 2)) (some 87) ([22, 16]) (some (22, sourceBody446_4, 446, 3))

def sourceBody446_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody446_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_5 sourceBody446_6

def sourceBody446_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_7 sourceBody446_0

def sourceBody446_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_3 sourceBody446_8

def sourceBody446_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_2 sourceBody446_9

def sourceBody446_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_0 sourceBody446_10

def sourceBody446_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_0 sourceBody446_11

def sourceBody446_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 26, Flapjack.WordLangExpHOL.const 8#64])

def sourceBody446_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 2)

def sourceBody446_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 20#64)

def sourceBody446_16 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody446_0, 446, 4)) (some 77) ([22, 16, 30]) (some (22, sourceBody446_4, 446, 5))

def sourceBody446_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_16 sourceBody446_6

def sourceBody446_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_17 sourceBody446_0

def sourceBody446_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_15 sourceBody446_18

def sourceBody446_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_14 sourceBody446_19

def sourceBody446_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_13 sourceBody446_20

def sourceBody446_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_0 sourceBody446_21

def sourceBody446_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_0 sourceBody446_22

def sourceBody446_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_12 sourceBody446_23

def sourceBody446_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 26, Flapjack.WordLangExpHOL.const 28#64])

def sourceBody446_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 4)

def sourceBody446_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody446_28 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody446_0, 446, 6)) (some 77) ([22, 16, 30]) (some (22, sourceBody446_4, 446, 7))

def sourceBody446_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_28 sourceBody446_6

def sourceBody446_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_29 sourceBody446_0

def sourceBody446_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_27 sourceBody446_30

def sourceBody446_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_26 sourceBody446_31

def sourceBody446_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_25 sourceBody446_32

def sourceBody446_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_0 sourceBody446_33

def sourceBody446_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_0 sourceBody446_34

def sourceBody446_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_24 sourceBody446_35

def sourceBody446_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 240#64]))

def sourceBody446_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 26)

def sourceBody446_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody446_40 : WordLangProgHOL (BitVec 64) :=
.call (some (([10, 22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody446_0, 446, 8)) (some 186) ([16, 30]) (some (16, sourceBody446_39, 446, 9))

def sourceBody446_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_40 sourceBody446_6

def sourceBody446_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_41 sourceBody446_0

def sourceBody446_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_38 sourceBody446_42

def sourceBody446_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_37 sourceBody446_43

def sourceBody446_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 10)

def sourceBody446_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody446_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody446_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody446_49 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 30 (Flapjack.WordRegImm.reg 8) sourceBody446_47 sourceBody446_48

def sourceBody446_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_49 sourceBody446_6

def sourceBody446_51 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 30)

def sourceBody446_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.load (Flapjack.WordLangExpHOL.var 22))

def sourceBody446_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 22, Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody446_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 22, Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody446_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 22, Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody446_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [16, 30, 8, 20]

def sourceBody446_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_56 sourceBody446_0

def sourceBody446_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_55 sourceBody446_57

def sourceBody446_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_54 sourceBody446_58

def sourceBody446_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_53 sourceBody446_59

def sourceBody446_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_52 sourceBody446_60

def sourceBody446_62 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 20 (Flapjack.WordRegImm.imm 0#64) sourceBody446_61 sourceBody446_0

def sourceBody446_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_62 sourceBody446_6

def sourceBody446_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_63 sourceBody446_0

def sourceBody446_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_51 sourceBody446_64

def sourceBody446_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_50 sourceBody446_65

def sourceBody446_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_46 sourceBody446_66

def sourceBody446_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_45 sourceBody446_67

def sourceBody446_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 2)

def sourceBody446_70 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 4)

def sourceBody446_71 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody446_72 : WordLangProgHOL (BitVec 64) :=
.call (some (([16, 30, 8, 20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody446_0, 446, 10)) (some 444) ([14, 28]) (some (14, sourceBody446_71, 446, 11))

def sourceBody446_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_72 sourceBody446_6

def sourceBody446_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_73 sourceBody446_0

def sourceBody446_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_70 sourceBody446_74

def sourceBody446_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_69 sourceBody446_75

def sourceBody446_77 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody446_78 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 28

def sourceBody446_79 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody446_0, 446, 12)) (some 68) ([28]) (some (28, sourceBody446_78, 446, 13))

def sourceBody446_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_79 sourceBody446_6

def sourceBody446_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_80 sourceBody446_0

def sourceBody446_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_77 sourceBody446_81

def sourceBody446_83 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 14)

def sourceBody446_84 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 16)

def sourceBody446_85 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 30)

def sourceBody446_86 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 8)

def sourceBody446_87 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 20)

def sourceBody446_88 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 12)

def sourceBody446_89 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 28) 6

def sourceBody446_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_89 sourceBody446_0

def sourceBody446_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_88 sourceBody446_90

def sourceBody446_92 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 24)

def sourceBody446_93 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 28, Flapjack.WordLangExpHOL.const 8#64]) 6

def sourceBody446_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_93 sourceBody446_0

def sourceBody446_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_92 sourceBody446_94

def sourceBody446_96 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 18)

def sourceBody446_97 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 28, Flapjack.WordLangExpHOL.const 16#64])
  6

def sourceBody446_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_97 sourceBody446_0

def sourceBody446_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_96 sourceBody446_98

def sourceBody446_100 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 32)

def sourceBody446_101 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 28, Flapjack.WordLangExpHOL.const 24#64])
  6

def sourceBody446_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_101 sourceBody446_0

def sourceBody446_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_100 sourceBody446_102

def sourceBody446_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_103 sourceBody446_0

def sourceBody446_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_99 sourceBody446_104

def sourceBody446_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_95 sourceBody446_105

def sourceBody446_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_91 sourceBody446_106

def sourceBody446_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_87 sourceBody446_107

def sourceBody446_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_0 sourceBody446_108

def sourceBody446_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_86 sourceBody446_109

def sourceBody446_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_0 sourceBody446_110

def sourceBody446_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_85 sourceBody446_111

def sourceBody446_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_0 sourceBody446_112

def sourceBody446_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_84 sourceBody446_113

def sourceBody446_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_0 sourceBody446_114

def sourceBody446_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_83 sourceBody446_115

def sourceBody446_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_0 sourceBody446_116

def sourceBody446_118 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 26)

def sourceBody446_119 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 224#64]))

def sourceBody446_120 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody446_121 : WordLangProgHOL (BitVec 64) :=
.call (some (([28]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody446_0, 446, 14)) (some 87) ([12, 24]) (some (12, sourceBody446_120, 446, 15))

def sourceBody446_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_121 sourceBody446_6

def sourceBody446_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_122 sourceBody446_0

def sourceBody446_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_119 sourceBody446_123

def sourceBody446_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_118 sourceBody446_124

def sourceBody446_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_0 sourceBody446_125

def sourceBody446_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_0 sourceBody446_126

def sourceBody446_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_117 sourceBody446_127

def sourceBody446_129 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 26, Flapjack.WordLangExpHOL.const 8#64])

def sourceBody446_130 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 2)

def sourceBody446_131 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 20#64)

def sourceBody446_132 : WordLangProgHOL (BitVec 64) :=
.call (some (([28]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody446_0, 446, 16)) (some 77) ([12, 24, 18]) (some (12, sourceBody446_120, 446, 17))

def sourceBody446_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_132 sourceBody446_6

def sourceBody446_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_133 sourceBody446_0

def sourceBody446_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_131 sourceBody446_134

def sourceBody446_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_130 sourceBody446_135

def sourceBody446_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_129 sourceBody446_136

def sourceBody446_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_0 sourceBody446_137

def sourceBody446_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_0 sourceBody446_138

def sourceBody446_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_128 sourceBody446_139

def sourceBody446_141 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 26, Flapjack.WordLangExpHOL.const 28#64])

def sourceBody446_142 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 4)

def sourceBody446_143 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody446_144 : WordLangProgHOL (BitVec 64) :=
.call (some (([28]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody446_0, 446, 18)) (some 77) ([12, 24, 18]) (some (12, sourceBody446_120, 446, 19))

def sourceBody446_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_144 sourceBody446_6

def sourceBody446_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_145 sourceBody446_0

def sourceBody446_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_143 sourceBody446_146

def sourceBody446_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_142 sourceBody446_147

def sourceBody446_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_141 sourceBody446_148

def sourceBody446_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_0 sourceBody446_149

def sourceBody446_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_0 sourceBody446_150

def sourceBody446_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_140 sourceBody446_151

def sourceBody446_153 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 240#64]))

def sourceBody446_154 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 26)

def sourceBody446_155 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 14)

def sourceBody446_156 : WordLangProgHOL (BitVec 64) :=
.call (some (([28]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody446_0, 446, 20)) (some 192) ([12, 24, 18]) (some (12, sourceBody446_120, 446, 21))

def sourceBody446_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_156 sourceBody446_6

def sourceBody446_158 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_157 sourceBody446_0

def sourceBody446_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_155 sourceBody446_158

def sourceBody446_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_154 sourceBody446_159

def sourceBody446_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_153 sourceBody446_160

def sourceBody446_162 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_0 sourceBody446_161

def sourceBody446_163 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_0 sourceBody446_162

def sourceBody446_164 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_152 sourceBody446_163

def sourceBody446_165 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 16)

def sourceBody446_166 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 30)

def sourceBody446_167 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 8)

def sourceBody446_168 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 20)

def sourceBody446_169 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [28, 12, 24, 18]

def sourceBody446_170 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_169 sourceBody446_0

def sourceBody446_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_168 sourceBody446_170

def sourceBody446_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_167 sourceBody446_171

def sourceBody446_173 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_166 sourceBody446_172

def sourceBody446_174 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_165 sourceBody446_173

def sourceBody446_175 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_164 sourceBody446_174

def sourceBody446_176 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_82 sourceBody446_175

def sourceBody446_177 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_0 sourceBody446_176

def sourceBody446_178 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_0 sourceBody446_177

def sourceBody446_179 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_76 sourceBody446_178

def sourceBody446_180 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_0 sourceBody446_179

def sourceBody446_181 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_0 sourceBody446_180

def sourceBody446_182 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_0 sourceBody446_181

def sourceBody446_183 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_0 sourceBody446_182

def sourceBody446_184 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_0 sourceBody446_183

def sourceBody446_185 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_0 sourceBody446_184

def sourceBody446_186 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_0 sourceBody446_185

def sourceBody446_187 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_0 sourceBody446_186

def sourceBody446_188 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_68 sourceBody446_187

def sourceBody446_189 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_44 sourceBody446_188

def sourceBody446_190 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_0 sourceBody446_189

def sourceBody446_191 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_0 sourceBody446_190

def sourceBody446_192 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_0 sourceBody446_191

def sourceBody446_193 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_0 sourceBody446_192

def sourceBody446_194 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_36 sourceBody446_193

def sourceBody446_195 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_1 sourceBody446_194

def sourceBody446_196 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody446_0 sourceBody446_195

def source446 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (446, 3, sourceBody446_196)
end InitECandidate.Proofs.WordStages
