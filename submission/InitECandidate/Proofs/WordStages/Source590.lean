import InitECandidate.Proofs.WordStages.Source574
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody590_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody590_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
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
        Flapjack.WordLangExpHOL.const 112#64]))

def sourceBody590_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody590_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody590_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody590_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody590_6 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 6 (Flapjack.WordRegImm.reg 20) sourceBody590_4 sourceBody590_5

def sourceBody590_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody590_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_6 sourceBody590_7

def sourceBody590_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 6)

def sourceBody590_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 32#64]))

def sourceBody590_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody590_12 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody590_0, 590, 2)) (some 401) ([6]) (some (6, sourceBody590_11, 590, 3))

def sourceBody590_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_12 sourceBody590_7

def sourceBody590_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_13 sourceBody590_0

def sourceBody590_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_10 sourceBody590_14

def sourceBody590_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 24)

def sourceBody590_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody590_18 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody590_0, 590, 4)) (some 412) ([20]) (some (20, sourceBody590_17, 590, 5))

def sourceBody590_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_18 sourceBody590_7

def sourceBody590_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_19 sourceBody590_0

def sourceBody590_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_16 sourceBody590_20

def sourceBody590_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody590_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody590_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody590_25 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.WordRegImm.reg 28) sourceBody590_23 sourceBody590_24

def sourceBody590_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_25 sourceBody590_7

def sourceBody590_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 14)

def sourceBody590_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 183600#64)

def sourceBody590_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody590_30 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody590_0, 590, 6)) (some 467) ([14]) (some (14, sourceBody590_29, 590, 7))

def sourceBody590_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_30 sourceBody590_7

def sourceBody590_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_31 sourceBody590_0

def sourceBody590_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_28 sourceBody590_32

def sourceBody590_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_0 sourceBody590_33

def sourceBody590_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_0 sourceBody590_34

def sourceBody590_36 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 4 (Flapjack.WordRegImm.imm 0#64) sourceBody590_35 sourceBody590_0

def sourceBody590_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_36 sourceBody590_7

def sourceBody590_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_37 sourceBody590_0

def sourceBody590_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_27 sourceBody590_38

def sourceBody590_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_26 sourceBody590_39

def sourceBody590_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_22 sourceBody590_40

def sourceBody590_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_9 sourceBody590_41

def sourceBody590_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [20]

def sourceBody590_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_43 sourceBody590_0

def sourceBody590_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_3 sourceBody590_44

def sourceBody590_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_42 sourceBody590_45

def sourceBody590_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_21 sourceBody590_46

def sourceBody590_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_0 sourceBody590_47

def sourceBody590_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_0 sourceBody590_48

def sourceBody590_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_15 sourceBody590_49

def sourceBody590_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_0 sourceBody590_50

def sourceBody590_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_0 sourceBody590_51

def sourceBody590_53 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.WordRegImm.imm 0#64) sourceBody590_52 sourceBody590_0

def sourceBody590_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_53 sourceBody590_7

def sourceBody590_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_54 sourceBody590_0

def sourceBody590_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_9 sourceBody590_55

def sourceBody590_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_8 sourceBody590_56

def sourceBody590_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_3 sourceBody590_57

def sourceBody590_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_2 sourceBody590_58

def sourceBody590_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 32#64]))

def sourceBody590_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 56#64]))

def sourceBody590_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 56#64],
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody590_63 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 56#64],
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody590_64 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 56#64],
        Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody590_65 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody590_0, 590, 8)) (some 102) ([20, 14, 28, 4]) (some (20, sourceBody590_17, 590, 9))

def sourceBody590_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_65 sourceBody590_7

def sourceBody590_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_66 sourceBody590_0

def sourceBody590_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_64 sourceBody590_67

def sourceBody590_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_63 sourceBody590_68

def sourceBody590_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_62 sourceBody590_69

def sourceBody590_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_61 sourceBody590_70

def sourceBody590_72 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 14 (Flapjack.WordRegImm.reg 28) sourceBody590_23 sourceBody590_24

def sourceBody590_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_72 sourceBody590_7

def sourceBody590_74 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 24)

def sourceBody590_75 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody590_0, 590, 10)) (some 414) ([14]) (some (14, sourceBody590_29, 590, 11))

def sourceBody590_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_75 sourceBody590_7

def sourceBody590_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_76 sourceBody590_0

def sourceBody590_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_74 sourceBody590_77

def sourceBody590_79 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 20)

def sourceBody590_80 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody590_81 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody590_82 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 28 (Flapjack.WordRegImm.reg 4) sourceBody590_81 sourceBody590_22

def sourceBody590_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_82 sourceBody590_7

def sourceBody590_84 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 28)

def sourceBody590_85 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 183600#64)

def sourceBody590_86 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 28

def sourceBody590_87 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody590_0, 590, 12)) (some 467) ([28]) (some (28, sourceBody590_86, 590, 13))

def sourceBody590_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_87 sourceBody590_7

def sourceBody590_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_88 sourceBody590_0

def sourceBody590_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_85 sourceBody590_89

def sourceBody590_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_0 sourceBody590_90

def sourceBody590_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_0 sourceBody590_91

def sourceBody590_93 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 18 (Flapjack.WordRegImm.imm 0#64) sourceBody590_92 sourceBody590_0

def sourceBody590_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_93 sourceBody590_7

def sourceBody590_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_94 sourceBody590_0

def sourceBody590_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_84 sourceBody590_95

def sourceBody590_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_83 sourceBody590_96

def sourceBody590_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_80 sourceBody590_97

def sourceBody590_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_79 sourceBody590_98

def sourceBody590_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_78 sourceBody590_99

def sourceBody590_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_0 sourceBody590_100

def sourceBody590_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_0 sourceBody590_101

def sourceBody590_103 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 4 (Flapjack.WordRegImm.imm 0#64) sourceBody590_102 sourceBody590_0

def sourceBody590_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_103 sourceBody590_7

def sourceBody590_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_104 sourceBody590_0

def sourceBody590_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_27 sourceBody590_105

def sourceBody590_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_73 sourceBody590_106

def sourceBody590_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_22 sourceBody590_107

def sourceBody590_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_9 sourceBody590_108

def sourceBody590_110 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 24)

def sourceBody590_111 : WordLangProgHOL (BitVec 64) :=
.call (some (([20, 14]), ((Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody590_0, 590, 14)) (some 561) ([28]) (some (28, sourceBody590_86, 590, 15))

def sourceBody590_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_111 sourceBody590_7

def sourceBody590_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_112 sourceBody590_0

def sourceBody590_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_110 sourceBody590_113

def sourceBody590_115 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 20)

def sourceBody590_116 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 14)

def sourceBody590_117 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody590_118 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody590_0, 590, 16)) (some 585) ([12, 26]) (some (12, sourceBody590_117, 590, 17))

def sourceBody590_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_118 sourceBody590_7

def sourceBody590_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_119 sourceBody590_0

def sourceBody590_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_116 sourceBody590_120

def sourceBody590_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_115 sourceBody590_121

def sourceBody590_123 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 18)

def sourceBody590_124 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody590_125 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody590_126 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody590_127 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 26 (Flapjack.WordRegImm.reg 8) sourceBody590_125 sourceBody590_126

def sourceBody590_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_127 sourceBody590_7

def sourceBody590_129 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 26)

def sourceBody590_130 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 24#64)

def sourceBody590_131 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 26

def sourceBody590_132 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody590_0, 590, 18)) (some 68) ([26]) (some (26, sourceBody590_131, 590, 19))

def sourceBody590_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_132 sourceBody590_7

def sourceBody590_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_133 sourceBody590_0

def sourceBody590_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_130 sourceBody590_134

def sourceBody590_136 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 12)

def sourceBody590_137 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 18)

def sourceBody590_138 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 20#64)

def sourceBody590_139 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody590_140 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody590_0, 590, 20)) (some 77) ([8, 22, 16]) (some (8, sourceBody590_139, 590, 21))

def sourceBody590_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_140 sourceBody590_7

def sourceBody590_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_141 sourceBody590_0

def sourceBody590_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_138 sourceBody590_142

def sourceBody590_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_137 sourceBody590_143

def sourceBody590_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_136 sourceBody590_144

def sourceBody590_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_0 sourceBody590_145

def sourceBody590_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_0 sourceBody590_146

def sourceBody590_148 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody590_0, 590, 22)) (some 489) ([8]) (some (8, sourceBody590_139, 590, 23))

def sourceBody590_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_148 sourceBody590_7

def sourceBody590_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_149 sourceBody590_0

def sourceBody590_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_136 sourceBody590_150

def sourceBody590_152 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody590_153 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody590_154 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody590_155 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 22 (Flapjack.WordRegImm.reg 16) sourceBody590_153 sourceBody590_154

def sourceBody590_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_155 sourceBody590_7

def sourceBody590_157 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 22)

def sourceBody590_158 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 100#64)

def sourceBody590_159 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 22

def sourceBody590_160 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody590_0, 590, 24)) (some 466) ([22]) (some (22, sourceBody590_159, 590, 25))

def sourceBody590_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_160 sourceBody590_7

def sourceBody590_162 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_161 sourceBody590_0

def sourceBody590_163 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_158 sourceBody590_162

def sourceBody590_164 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_0 sourceBody590_163

def sourceBody590_165 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_0 sourceBody590_164

def sourceBody590_166 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 3000#64)

def sourceBody590_167 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody590_0, 590, 26)) (some 466) ([22]) (some (22, sourceBody590_159, 590, 27))

def sourceBody590_168 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_167 sourceBody590_7

def sourceBody590_169 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_168 sourceBody590_0

def sourceBody590_170 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_166 sourceBody590_169

def sourceBody590_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_0 sourceBody590_170

def sourceBody590_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_0 sourceBody590_171

def sourceBody590_173 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 12)

def sourceBody590_174 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody590_0, 590, 28)) (some 490) ([22]) (some (22, sourceBody590_159, 590, 29))

def sourceBody590_175 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_174 sourceBody590_7

def sourceBody590_176 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_175 sourceBody590_0

def sourceBody590_177 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_173 sourceBody590_176

def sourceBody590_178 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_0 sourceBody590_177

def sourceBody590_179 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_0 sourceBody590_178

def sourceBody590_180 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_172 sourceBody590_179

def sourceBody590_181 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 30 (Flapjack.WordRegImm.imm 0#64) sourceBody590_165 sourceBody590_180

def sourceBody590_182 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_181 sourceBody590_7

def sourceBody590_183 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_182 sourceBody590_0

def sourceBody590_184 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_157 sourceBody590_183

def sourceBody590_185 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_156 sourceBody590_184

def sourceBody590_186 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_152 sourceBody590_185

def sourceBody590_187 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_129 sourceBody590_186

def sourceBody590_188 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 12)

def sourceBody590_189 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody590_190 : WordLangProgHOL (BitVec 64) :=
.call (some (([8, 22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody590_0, 590, 30)) (some 561) ([16]) (some (16, sourceBody590_189, 590, 31))

def sourceBody590_191 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_190 sourceBody590_7

def sourceBody590_192 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_191 sourceBody590_0

def sourceBody590_193 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_188 sourceBody590_192

def sourceBody590_194 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 8)

def sourceBody590_195 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_194 sourceBody590_0

def sourceBody590_196 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_195 sourceBody590_0

def sourceBody590_197 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 22)

def sourceBody590_198 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_197 sourceBody590_0

def sourceBody590_199 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_198 sourceBody590_0

def sourceBody590_200 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_196 sourceBody590_199

def sourceBody590_201 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 168#64])

def sourceBody590_202 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody590_203 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 30)

def sourceBody590_204 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 16) 2

def sourceBody590_205 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_204 sourceBody590_0

def sourceBody590_206 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_203 sourceBody590_205

def sourceBody590_207 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_206 sourceBody590_0

def sourceBody590_208 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_202 sourceBody590_207

def sourceBody590_209 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_0 sourceBody590_208

def sourceBody590_210 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_201 sourceBody590_209

def sourceBody590_211 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_0 sourceBody590_210

def sourceBody590_212 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_200 sourceBody590_211

def sourceBody590_213 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 104#64])

def sourceBody590_214 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 12)

def sourceBody590_215 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_214 sourceBody590_207

def sourceBody590_216 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_0 sourceBody590_215

def sourceBody590_217 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_213 sourceBody590_216

def sourceBody590_218 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_0 sourceBody590_217

def sourceBody590_219 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_212 sourceBody590_218

def sourceBody590_220 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_193 sourceBody590_219

def sourceBody590_221 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_0 sourceBody590_220

def sourceBody590_222 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_0 sourceBody590_221

def sourceBody590_223 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_0 sourceBody590_222

def sourceBody590_224 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_0 sourceBody590_223

def sourceBody590_225 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_187 sourceBody590_224

def sourceBody590_226 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_151 sourceBody590_225

def sourceBody590_227 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_0 sourceBody590_226

def sourceBody590_228 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_0 sourceBody590_227

def sourceBody590_229 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_147 sourceBody590_228

def sourceBody590_230 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_135 sourceBody590_229

def sourceBody590_231 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_0 sourceBody590_230

def sourceBody590_232 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_0 sourceBody590_231

def sourceBody590_233 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 22 (Flapjack.WordRegImm.imm 0#64) sourceBody590_232 sourceBody590_0

def sourceBody590_234 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_233 sourceBody590_7

def sourceBody590_235 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_234 sourceBody590_0

def sourceBody590_236 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_129 sourceBody590_235

def sourceBody590_237 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_128 sourceBody590_236

def sourceBody590_238 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_124 sourceBody590_237

def sourceBody590_239 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_123 sourceBody590_238

def sourceBody590_240 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 112#64])

def sourceBody590_241 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 28)

def sourceBody590_242 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 26)

def sourceBody590_243 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 12) 8

def sourceBody590_244 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_243 sourceBody590_0

def sourceBody590_245 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_242 sourceBody590_244

def sourceBody590_246 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_245 sourceBody590_0

def sourceBody590_247 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_241 sourceBody590_246

def sourceBody590_248 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_0 sourceBody590_247

def sourceBody590_249 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_240 sourceBody590_248

def sourceBody590_250 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_0 sourceBody590_249

def sourceBody590_251 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_239 sourceBody590_250

def sourceBody590_252 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 120#64])

def sourceBody590_253 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 4)

def sourceBody590_254 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_253 sourceBody590_246

def sourceBody590_255 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_0 sourceBody590_254

def sourceBody590_256 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_252 sourceBody590_255

def sourceBody590_257 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_0 sourceBody590_256

def sourceBody590_258 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_251 sourceBody590_257

def sourceBody590_259 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 256#64]),
      Flapjack.WordLangExpHOL.const 48#64])

def sourceBody590_260 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_259 sourceBody590_248

def sourceBody590_261 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_0 sourceBody590_260

def sourceBody590_262 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_258 sourceBody590_261

def sourceBody590_263 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 256#64]),
      Flapjack.WordLangExpHOL.const 56#64])

def sourceBody590_264 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_263 sourceBody590_255

def sourceBody590_265 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_0 sourceBody590_264

def sourceBody590_266 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_262 sourceBody590_265

def sourceBody590_267 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 4)

def sourceBody590_268 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody590_0, 590, 32)) (some 481) ([26, 8]) (some (26, sourceBody590_131, 590, 33))

def sourceBody590_269 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_268 sourceBody590_7

def sourceBody590_270 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_269 sourceBody590_0

def sourceBody590_271 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_267 sourceBody590_270

def sourceBody590_272 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_241 sourceBody590_271

def sourceBody590_273 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 256#64]),
      Flapjack.WordLangExpHOL.const 80#64])

def sourceBody590_274 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 8)

def sourceBody590_275 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 26) 22

def sourceBody590_276 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_275 sourceBody590_0

def sourceBody590_277 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_274 sourceBody590_276

def sourceBody590_278 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_277 sourceBody590_0

def sourceBody590_279 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_136 sourceBody590_278

def sourceBody590_280 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_0 sourceBody590_279

def sourceBody590_281 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_273 sourceBody590_280

def sourceBody590_282 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_0 sourceBody590_281

def sourceBody590_283 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [26]

def sourceBody590_284 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_283 sourceBody590_0

def sourceBody590_285 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_126 sourceBody590_284

def sourceBody590_286 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_282 sourceBody590_285

def sourceBody590_287 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_272 sourceBody590_286

def sourceBody590_288 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_0 sourceBody590_287

def sourceBody590_289 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_0 sourceBody590_288

def sourceBody590_290 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_266 sourceBody590_289

def sourceBody590_291 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_122 sourceBody590_290

def sourceBody590_292 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_0 sourceBody590_291

def sourceBody590_293 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_0 sourceBody590_292

def sourceBody590_294 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_27 sourceBody590_293

def sourceBody590_295 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_0 sourceBody590_294

def sourceBody590_296 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_79 sourceBody590_295

def sourceBody590_297 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_0 sourceBody590_296

def sourceBody590_298 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_114 sourceBody590_297

def sourceBody590_299 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_0 sourceBody590_298

def sourceBody590_300 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_0 sourceBody590_299

def sourceBody590_301 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_0 sourceBody590_300

def sourceBody590_302 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_0 sourceBody590_301

def sourceBody590_303 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_109 sourceBody590_302

def sourceBody590_304 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_71 sourceBody590_303

def sourceBody590_305 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_0 sourceBody590_304

def sourceBody590_306 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_0 sourceBody590_305

def sourceBody590_307 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_60 sourceBody590_306

def sourceBody590_308 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_0 sourceBody590_307

def sourceBody590_309 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_59 sourceBody590_308

def sourceBody590_310 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_1 sourceBody590_309

def sourceBody590_311 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody590_0 sourceBody590_310

def source590 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (590, 1, sourceBody590_311)
end InitECandidate.Proofs.WordStages
