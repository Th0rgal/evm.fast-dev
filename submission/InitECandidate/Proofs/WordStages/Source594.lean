import InitECandidate.Proofs.WordStages.Source578
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody594_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody594_1 : WordLangProgHOL (BitVec 64) :=
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
        Flapjack.WordLangExpHOL.const 112#64]))

def sourceBody594_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 136#64]))

def sourceBody594_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody594_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody594_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody594_6 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 4 (Flapjack.WordRegImm.reg 18) sourceBody594_4 sourceBody594_5

def sourceBody594_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody594_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_6 sourceBody594_7

def sourceBody594_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 4)

def sourceBody594_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 56#64]))

def sourceBody594_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 56#64],
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody594_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 56#64],
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody594_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 56#64],
        Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody594_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 22)

def sourceBody594_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 4)

def sourceBody594_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 18)

def sourceBody594_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 12)

def sourceBody594_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 2

def sourceBody594_19 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody594_0, 594, 2)) (some 102) ([2, 16, 10, 24]) (some (2, sourceBody594_18, 594, 3))

def sourceBody594_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_19 sourceBody594_7

def sourceBody594_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_20 sourceBody594_0

def sourceBody594_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_17 sourceBody594_21

def sourceBody594_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_16 sourceBody594_22

def sourceBody594_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_15 sourceBody594_23

def sourceBody594_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_14 sourceBody594_24

def sourceBody594_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 26)

def sourceBody594_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody594_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody594_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody594_30 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 16 (Flapjack.WordRegImm.reg 10) sourceBody594_28 sourceBody594_29

def sourceBody594_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_30 sourceBody594_7

def sourceBody594_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 16)

def sourceBody594_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody594_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 32#64]))

def sourceBody594_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 22)

def sourceBody594_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 4)

def sourceBody594_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 18)

def sourceBody594_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 12)

def sourceBody594_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody594_40 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody594_0, 594, 4)) (some 423) ([16, 10, 24, 6, 20, 14]) (some (16, sourceBody594_39, 594, 5))

def sourceBody594_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_40 sourceBody594_7

def sourceBody594_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_41 sourceBody594_0

def sourceBody594_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_38 sourceBody594_42

def sourceBody594_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_37 sourceBody594_43

def sourceBody594_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_36 sourceBody594_44

def sourceBody594_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_35 sourceBody594_45

def sourceBody594_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_34 sourceBody594_46

def sourceBody594_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_33 sourceBody594_47

def sourceBody594_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_0 sourceBody594_48

def sourceBody594_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_0 sourceBody594_49

def sourceBody594_51 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 20#64)

def sourceBody594_52 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody594_0, 594, 6)) (some 79) ([16, 10, 24]) (some (16, sourceBody594_39, 594, 7))

def sourceBody594_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_52 sourceBody594_7

def sourceBody594_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_53 sourceBody594_0

def sourceBody594_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_51 sourceBody594_54

def sourceBody594_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_34 sourceBody594_55

def sourceBody594_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_33 sourceBody594_56

def sourceBody594_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 2)

def sourceBody594_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody594_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody594_61 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 10 (Flapjack.WordRegImm.reg 24) sourceBody594_60 sourceBody594_27

def sourceBody594_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_61 sourceBody594_7

def sourceBody594_63 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 10)

def sourceBody594_64 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody594_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 32#64]))

def sourceBody594_66 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 22)

def sourceBody594_67 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 4)

def sourceBody594_68 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 18)

def sourceBody594_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 12)

def sourceBody594_70 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody594_71 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody594_0, 594, 8)) (some 581) ([10, 24, 6, 20, 14, 28]) (some (10, sourceBody594_70, 594, 9))

def sourceBody594_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_71 sourceBody594_7

def sourceBody594_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_72 sourceBody594_0

def sourceBody594_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_69 sourceBody594_73

def sourceBody594_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_68 sourceBody594_74

def sourceBody594_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_67 sourceBody594_75

def sourceBody594_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_66 sourceBody594_76

def sourceBody594_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_65 sourceBody594_77

def sourceBody594_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_64 sourceBody594_78

def sourceBody594_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_0 sourceBody594_79

def sourceBody594_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_0 sourceBody594_80

def sourceBody594_82 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.WordRegImm.imm 0#64) sourceBody594_81 sourceBody594_0

def sourceBody594_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_82 sourceBody594_7

def sourceBody594_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_83 sourceBody594_0

def sourceBody594_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_63 sourceBody594_84

def sourceBody594_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_62 sourceBody594_85

def sourceBody594_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_59 sourceBody594_86

def sourceBody594_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_58 sourceBody594_87

def sourceBody594_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_57 sourceBody594_88

def sourceBody594_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_0 sourceBody594_89

def sourceBody594_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_0 sourceBody594_90

def sourceBody594_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_50 sourceBody594_91

def sourceBody594_93 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 24 (Flapjack.WordRegImm.imm 0#64) sourceBody594_92 sourceBody594_0

def sourceBody594_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_93 sourceBody594_7

def sourceBody594_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_94 sourceBody594_0

def sourceBody594_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_32 sourceBody594_95

def sourceBody594_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_31 sourceBody594_96

def sourceBody594_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_27 sourceBody594_97

def sourceBody594_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_26 sourceBody594_98

def sourceBody594_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_25 sourceBody594_99

def sourceBody594_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_0 sourceBody594_100

def sourceBody594_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_0 sourceBody594_101

def sourceBody594_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_13 sourceBody594_102

def sourceBody594_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_0 sourceBody594_103

def sourceBody594_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_12 sourceBody594_104

def sourceBody594_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_0 sourceBody594_105

def sourceBody594_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_11 sourceBody594_106

def sourceBody594_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_0 sourceBody594_107

def sourceBody594_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_10 sourceBody594_108

def sourceBody594_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_0 sourceBody594_109

def sourceBody594_111 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.imm 0#64) sourceBody594_110 sourceBody594_0

def sourceBody594_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_111 sourceBody594_7

def sourceBody594_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_112 sourceBody594_0

def sourceBody594_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_9 sourceBody594_113

def sourceBody594_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_8 sourceBody594_114

def sourceBody594_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_3 sourceBody594_115

def sourceBody594_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_2 sourceBody594_116

def sourceBody594_118 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 104#64]))

def sourceBody594_119 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 22)

def sourceBody594_120 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody594_121 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody594_122 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 18 (Flapjack.WordRegImm.reg 12) sourceBody594_121 sourceBody594_3

def sourceBody594_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_122 sourceBody594_7

def sourceBody594_124 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 18)

def sourceBody594_125 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody594_126 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody594_0, 594, 10)) (some 825) ([18]) (some (18, sourceBody594_125, 594, 11))

def sourceBody594_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_126 sourceBody594_7

def sourceBody594_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_127 sourceBody594_0

def sourceBody594_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_119 sourceBody594_128

def sourceBody594_130 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody594_131 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody594_132 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.reg 26) sourceBody594_131 sourceBody594_120

def sourceBody594_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_132 sourceBody594_7

def sourceBody594_134 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 12)

def sourceBody594_135 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 168#64]))

def sourceBody594_136 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 12 (Flapjack.WordRegImm.reg 26) sourceBody594_131 sourceBody594_120

def sourceBody594_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_136 sourceBody594_7

def sourceBody594_138 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody594_139 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody594_0, 594, 12)) (some 833) ([12]) (some (12, sourceBody594_138, 594, 13))

def sourceBody594_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_139 sourceBody594_7

def sourceBody594_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_140 sourceBody594_0

def sourceBody594_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_9 sourceBody594_141

def sourceBody594_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_0 sourceBody594_142

def sourceBody594_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_0 sourceBody594_143

def sourceBody594_145 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 2 (Flapjack.WordRegImm.imm 0#64) sourceBody594_144 sourceBody594_0

def sourceBody594_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_145 sourceBody594_7

def sourceBody594_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_146 sourceBody594_0

def sourceBody594_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_134 sourceBody594_147

def sourceBody594_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_137 sourceBody594_148

def sourceBody594_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_130 sourceBody594_149

def sourceBody594_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_135 sourceBody594_150

def sourceBody594_152 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [18]

def sourceBody594_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_152 sourceBody594_0

def sourceBody594_154 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_121 sourceBody594_153

def sourceBody594_155 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_151 sourceBody594_154

def sourceBody594_156 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 2 (Flapjack.WordRegImm.imm 0#64) sourceBody594_155 sourceBody594_0

def sourceBody594_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_156 sourceBody594_7

def sourceBody594_158 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_157 sourceBody594_0

def sourceBody594_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_134 sourceBody594_158

def sourceBody594_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_133 sourceBody594_159

def sourceBody594_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_130 sourceBody594_160

def sourceBody594_162 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_9 sourceBody594_161

def sourceBody594_163 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_129 sourceBody594_162

def sourceBody594_164 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_0 sourceBody594_163

def sourceBody594_165 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_0 sourceBody594_164

def sourceBody594_166 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 26 (Flapjack.WordRegImm.imm 0#64) sourceBody594_165 sourceBody594_0

def sourceBody594_167 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_166 sourceBody594_7

def sourceBody594_168 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_167 sourceBody594_0

def sourceBody594_169 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_124 sourceBody594_168

def sourceBody594_170 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_123 sourceBody594_169

def sourceBody594_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_120 sourceBody594_170

def sourceBody594_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_119 sourceBody594_171

def sourceBody594_173 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [4]

def sourceBody594_174 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_173 sourceBody594_0

def sourceBody594_175 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_5 sourceBody594_174

def sourceBody594_176 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_172 sourceBody594_175

def sourceBody594_177 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_118 sourceBody594_176

def sourceBody594_178 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_0 sourceBody594_177

def sourceBody594_179 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_117 sourceBody594_178

def sourceBody594_180 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_1 sourceBody594_179

def sourceBody594_181 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody594_0 sourceBody594_180

def source594 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (594, 1, sourceBody594_181)
end InitECandidate.Proofs.WordStages
