import InitECandidate.Proofs.WordStages.Source265
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody281_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 96#64]))

def sourceBody281_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody281_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody281_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody281_4 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 10 (Flapjack.WordRegImm.reg 22) sourceBody281_2 sourceBody281_3

def sourceBody281_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody281_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_4 sourceBody281_5

def sourceBody281_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 10)

def sourceBody281_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody281_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 20#64)

def sourceBody281_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 26)

def sourceBody281_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_10 sourceBody281_8

def sourceBody281_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_11 sourceBody281_8

def sourceBody281_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_9 sourceBody281_12

def sourceBody281_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_8 sourceBody281_13

def sourceBody281_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 4#64)

def sourceBody281_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 26

def sourceBody281_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_15 sourceBody281_16

def sourceBody281_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_14 sourceBody281_17

def sourceBody281_19 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 16 (Flapjack.WordRegImm.imm 0#64) sourceBody281_18 sourceBody281_8

def sourceBody281_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_19 sourceBody281_5

def sourceBody281_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_20 sourceBody281_8

def sourceBody281_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_7 sourceBody281_21

def sourceBody281_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_6 sourceBody281_22

def sourceBody281_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_1 sourceBody281_23

def sourceBody281_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_0 sourceBody281_24

def sourceBody281_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 2)

def sourceBody281_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody281_28 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody281_8, 281, 2)) (some 277) ([10]) (some (10, sourceBody281_27, 281, 3))

def sourceBody281_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_28 sourceBody281_5

def sourceBody281_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_29 sourceBody281_8

def sourceBody281_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_26 sourceBody281_30

def sourceBody281_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 208#64]))

def sourceBody281_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 26)

def sourceBody281_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody281_35 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 22 (Flapjack.WordRegImm.reg 16) sourceBody281_1 sourceBody281_34

def sourceBody281_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_35 sourceBody281_5

def sourceBody281_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 22)

def sourceBody281_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 21#64)

def sourceBody281_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 10)

def sourceBody281_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_39 sourceBody281_8

def sourceBody281_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_40 sourceBody281_8

def sourceBody281_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_38 sourceBody281_41

def sourceBody281_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_8 sourceBody281_42

def sourceBody281_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 4#64)

def sourceBody281_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_44 sourceBody281_27

def sourceBody281_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_43 sourceBody281_45

def sourceBody281_47 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 30 (Flapjack.WordRegImm.imm 0#64) sourceBody281_46 sourceBody281_8

def sourceBody281_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_47 sourceBody281_5

def sourceBody281_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_48 sourceBody281_8

def sourceBody281_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_37 sourceBody281_49

def sourceBody281_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_36 sourceBody281_50

def sourceBody281_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_33 sourceBody281_51

def sourceBody281_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_32 sourceBody281_52

def sourceBody281_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 104#64]))

def sourceBody281_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 112#64]))

def sourceBody281_56 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 22 (Flapjack.WordRegImm.reg 16) sourceBody281_1 sourceBody281_34

def sourceBody281_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_56 sourceBody281_5

def sourceBody281_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 22#64)

def sourceBody281_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_58 sourceBody281_41

def sourceBody281_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_8 sourceBody281_59

def sourceBody281_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_60 sourceBody281_45

def sourceBody281_62 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 30 (Flapjack.WordRegImm.imm 0#64) sourceBody281_61 sourceBody281_8

def sourceBody281_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_62 sourceBody281_5

def sourceBody281_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_63 sourceBody281_8

def sourceBody281_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_37 sourceBody281_64

def sourceBody281_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_57 sourceBody281_65

def sourceBody281_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_55 sourceBody281_66

def sourceBody281_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_54 sourceBody281_67

def sourceBody281_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_53 sourceBody281_68

def sourceBody281_70 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 104#64]))

def sourceBody281_71 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 104#64]))

def sourceBody281_72 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 112#64]))

def sourceBody281_73 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 160#64]))

def sourceBody281_74 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 160#64],
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody281_75 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 160#64],
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody281_76 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 160#64],
        Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody281_77 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody281_78 : WordLangProgHOL (BitVec 64) :=
.call (some (([10, 22, 16, 30]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody281_8, 281, 4)) (some 279) ([8, 20, 14, 28, 12, 24, 18]) (some (8, sourceBody281_77, 281, 5))

def sourceBody281_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_78 sourceBody281_5

def sourceBody281_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_79 sourceBody281_8

def sourceBody281_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_76 sourceBody281_80

def sourceBody281_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_75 sourceBody281_81

def sourceBody281_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_74 sourceBody281_82

def sourceBody281_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_73 sourceBody281_83

def sourceBody281_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_72 sourceBody281_84

def sourceBody281_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_71 sourceBody281_85

def sourceBody281_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_70 sourceBody281_86

def sourceBody281_88 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 10)

def sourceBody281_89 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 22)

def sourceBody281_90 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 16)

def sourceBody281_91 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 30)

def sourceBody281_92 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 160#64]))

def sourceBody281_93 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 160#64],
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody281_94 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 160#64],
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody281_95 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 160#64],
        Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody281_96 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody281_97 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody281_8, 281, 6)) (some 105) ([20, 14, 28, 12, 24, 18, 32, 6]) (some (20, sourceBody281_96, 281, 7))

def sourceBody281_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_97 sourceBody281_5

def sourceBody281_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_98 sourceBody281_8

def sourceBody281_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_95 sourceBody281_99

def sourceBody281_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_94 sourceBody281_100

def sourceBody281_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_93 sourceBody281_101

def sourceBody281_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_92 sourceBody281_102

def sourceBody281_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_91 sourceBody281_103

def sourceBody281_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_90 sourceBody281_104

def sourceBody281_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_89 sourceBody281_105

def sourceBody281_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_88 sourceBody281_106

def sourceBody281_108 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 8)

def sourceBody281_109 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody281_110 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody281_111 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody281_112 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 14 (Flapjack.WordRegImm.reg 28) sourceBody281_110 sourceBody281_111

def sourceBody281_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_112 sourceBody281_5

def sourceBody281_114 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 14)

def sourceBody281_115 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 23#64)

def sourceBody281_116 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 20)

def sourceBody281_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_116 sourceBody281_8

def sourceBody281_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_117 sourceBody281_8

def sourceBody281_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_115 sourceBody281_118

def sourceBody281_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_8 sourceBody281_119

def sourceBody281_121 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 4#64)

def sourceBody281_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_121 sourceBody281_96

def sourceBody281_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_120 sourceBody281_122

def sourceBody281_124 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.imm 0#64) sourceBody281_123 sourceBody281_8

def sourceBody281_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_124 sourceBody281_5

def sourceBody281_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_125 sourceBody281_8

def sourceBody281_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_114 sourceBody281_126

def sourceBody281_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_113 sourceBody281_127

def sourceBody281_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_109 sourceBody281_128

def sourceBody281_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_108 sourceBody281_129

def sourceBody281_131 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 120#64]))

def sourceBody281_132 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 120#64]))

def sourceBody281_133 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notLower) 14 (Flapjack.WordRegImm.reg 28) sourceBody281_110 sourceBody281_111

def sourceBody281_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_133 sourceBody281_5

def sourceBody281_135 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 24#64)

def sourceBody281_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_135 sourceBody281_118

def sourceBody281_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_8 sourceBody281_136

def sourceBody281_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_137 sourceBody281_122

def sourceBody281_139 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.imm 0#64) sourceBody281_138 sourceBody281_8

def sourceBody281_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_139 sourceBody281_5

def sourceBody281_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_140 sourceBody281_8

def sourceBody281_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_114 sourceBody281_141

def sourceBody281_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_134 sourceBody281_142

def sourceBody281_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_132 sourceBody281_143

def sourceBody281_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_131 sourceBody281_144

def sourceBody281_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_130 sourceBody281_145

def sourceBody281_147 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 96#64]))

def sourceBody281_148 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 96#64]),
      Flapjack.WordLangExpHOL.const 1#64])

def sourceBody281_149 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.WordRegImm.reg 28) sourceBody281_110 sourceBody281_111

def sourceBody281_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_149 sourceBody281_5

def sourceBody281_151 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 25#64)

def sourceBody281_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_151 sourceBody281_118

def sourceBody281_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_8 sourceBody281_152

def sourceBody281_154 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_153 sourceBody281_122

def sourceBody281_155 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.imm 0#64) sourceBody281_154 sourceBody281_8

def sourceBody281_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_155 sourceBody281_5

def sourceBody281_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_156 sourceBody281_8

def sourceBody281_158 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_114 sourceBody281_157

def sourceBody281_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_150 sourceBody281_158

def sourceBody281_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_148 sourceBody281_159

def sourceBody281_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_147 sourceBody281_160

def sourceBody281_162 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_146 sourceBody281_161

def sourceBody281_163 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody281_164 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 136#64]))

def sourceBody281_165 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 14 (Flapjack.WordRegImm.reg 28) sourceBody281_110 sourceBody281_111

def sourceBody281_166 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_165 sourceBody281_5

def sourceBody281_167 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 26#64)

def sourceBody281_168 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_167 sourceBody281_118

def sourceBody281_169 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_8 sourceBody281_168

def sourceBody281_170 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_169 sourceBody281_122

def sourceBody281_171 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.imm 0#64) sourceBody281_170 sourceBody281_8

def sourceBody281_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_171 sourceBody281_5

def sourceBody281_173 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_172 sourceBody281_8

def sourceBody281_174 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_114 sourceBody281_173

def sourceBody281_175 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_166 sourceBody281_174

def sourceBody281_176 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_164 sourceBody281_175

def sourceBody281_177 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_163 sourceBody281_176

def sourceBody281_178 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_162 sourceBody281_177

def sourceBody281_179 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 64#64]))

def sourceBody281_180 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 64#64],
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody281_181 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 64#64],
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody281_182 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 64#64],
        Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody281_183 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody281_184 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody281_8, 281, 8)) (some 102) ([14, 28, 12, 24]) (some (14, sourceBody281_183, 281, 9))

def sourceBody281_185 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_184 sourceBody281_5

def sourceBody281_186 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_185 sourceBody281_8

def sourceBody281_187 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_182 sourceBody281_186

def sourceBody281_188 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_181 sourceBody281_187

def sourceBody281_189 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_180 sourceBody281_188

def sourceBody281_190 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_179 sourceBody281_189

def sourceBody281_191 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 20)

def sourceBody281_192 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody281_193 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody281_194 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 28 (Flapjack.WordRegImm.reg 12) sourceBody281_193 sourceBody281_109

def sourceBody281_195 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_194 sourceBody281_5

def sourceBody281_196 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 28)

def sourceBody281_197 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 27#64)

def sourceBody281_198 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 14)

def sourceBody281_199 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_198 sourceBody281_8

def sourceBody281_200 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_199 sourceBody281_8

def sourceBody281_201 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_197 sourceBody281_200

def sourceBody281_202 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_8 sourceBody281_201

def sourceBody281_203 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 4#64)

def sourceBody281_204 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_203 sourceBody281_183

def sourceBody281_205 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_202 sourceBody281_204

def sourceBody281_206 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 24 (Flapjack.WordRegImm.imm 0#64) sourceBody281_205 sourceBody281_8

def sourceBody281_207 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_206 sourceBody281_5

def sourceBody281_208 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_207 sourceBody281_8

def sourceBody281_209 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_196 sourceBody281_208

def sourceBody281_210 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_195 sourceBody281_209

def sourceBody281_211 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_192 sourceBody281_210

def sourceBody281_212 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_191 sourceBody281_211

def sourceBody281_213 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 152#64]))

def sourceBody281_214 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 120#64]))

def sourceBody281_215 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 8#64)

def sourceBody281_216 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody281_8, 281, 10)) (some 79) ([14, 28, 12]) (some (14, sourceBody281_183, 281, 11))

def sourceBody281_217 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_216 sourceBody281_5

def sourceBody281_218 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_217 sourceBody281_8

def sourceBody281_219 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_215 sourceBody281_218

def sourceBody281_220 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_214 sourceBody281_219

def sourceBody281_221 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_213 sourceBody281_220

def sourceBody281_222 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_212 sourceBody281_221

def sourceBody281_223 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 8)

def sourceBody281_224 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 28#64)

def sourceBody281_225 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_224 sourceBody281_200

def sourceBody281_226 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_8 sourceBody281_225

def sourceBody281_227 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_226 sourceBody281_204

def sourceBody281_228 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 24 (Flapjack.WordRegImm.imm 0#64) sourceBody281_227 sourceBody281_8

def sourceBody281_229 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_228 sourceBody281_5

def sourceBody281_230 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_229 sourceBody281_8

def sourceBody281_231 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_196 sourceBody281_230

def sourceBody281_232 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_195 sourceBody281_231

def sourceBody281_233 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_192 sourceBody281_232

def sourceBody281_234 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_223 sourceBody281_233

def sourceBody281_235 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_222 sourceBody281_234

def sourceBody281_236 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 28

def sourceBody281_237 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody281_8, 281, 12)) (some 69) ([]) (some (28, sourceBody281_236, 281, 13))

def sourceBody281_238 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_237 sourceBody281_5

def sourceBody281_239 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_238 sourceBody281_8

def sourceBody281_240 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 64#64)

def sourceBody281_241 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody281_242 : WordLangProgHOL (BitVec 64) :=
.call (some (([28]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
      (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody281_8, 281, 14)) (some 68) ([12]) (some (12, sourceBody281_241, 281, 15))

def sourceBody281_243 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_242 sourceBody281_5

def sourceBody281_244 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_243 sourceBody281_8

def sourceBody281_245 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_240 sourceBody281_244

def sourceBody281_246 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 28)

def sourceBody281_247 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 192#64)

def sourceBody281_248 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.store8 24 (Flapjack.WordLangAddr.addr 12 0#64))

def sourceBody281_249 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_248 sourceBody281_8

def sourceBody281_250 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_247 sourceBody281_249

def sourceBody281_251 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_246 sourceBody281_250

def sourceBody281_252 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody281_253 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 28, Flapjack.WordLangExpHOL.const 32#64])

def sourceBody281_254 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 24

def sourceBody281_255 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody281_8, 281, 16)) (some 158) ([24, 18, 32]) (some (24, sourceBody281_254, 281, 17))

def sourceBody281_256 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_255 sourceBody281_5

def sourceBody281_257 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_256 sourceBody281_8

def sourceBody281_258 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_253 sourceBody281_257

def sourceBody281_259 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_252 sourceBody281_258

def sourceBody281_260 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_196 sourceBody281_259

def sourceBody281_261 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_8 sourceBody281_260

def sourceBody281_262 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_8 sourceBody281_261

def sourceBody281_263 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_251 sourceBody281_262

def sourceBody281_264 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody281_265 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 28, Flapjack.WordLangExpHOL.const 32#64])

def sourceBody281_266 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody281_267 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody281_8, 281, 18)) (some 79) ([12, 24, 18]) (some (12, sourceBody281_241, 281, 19))

def sourceBody281_268 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_267 sourceBody281_5

def sourceBody281_269 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_268 sourceBody281_8

def sourceBody281_270 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_266 sourceBody281_269

def sourceBody281_271 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_265 sourceBody281_270

def sourceBody281_272 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_264 sourceBody281_271

def sourceBody281_273 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_263 sourceBody281_272

def sourceBody281_274 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 8)

def sourceBody281_275 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody281_276 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody281_277 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody281_278 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 24 (Flapjack.WordRegImm.reg 18) sourceBody281_276 sourceBody281_277

def sourceBody281_279 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_278 sourceBody281_5

def sourceBody281_280 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 24)

def sourceBody281_281 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 14)

def sourceBody281_282 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody281_8, 281, 20)) (some 70) ([24]) (some (24, sourceBody281_254, 281, 21))

def sourceBody281_283 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_282 sourceBody281_5

def sourceBody281_284 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_283 sourceBody281_8

def sourceBody281_285 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_281 sourceBody281_284

def sourceBody281_286 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_8 sourceBody281_285

def sourceBody281_287 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_8 sourceBody281_286

def sourceBody281_288 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 29#64)

def sourceBody281_289 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 12)

def sourceBody281_290 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_289 sourceBody281_8

def sourceBody281_291 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_290 sourceBody281_8

def sourceBody281_292 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_288 sourceBody281_291

def sourceBody281_293 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_8 sourceBody281_292

def sourceBody281_294 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 4#64)

def sourceBody281_295 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_294 sourceBody281_241

def sourceBody281_296 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_293 sourceBody281_295

def sourceBody281_297 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_287 sourceBody281_296

def sourceBody281_298 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 32 (Flapjack.WordRegImm.imm 0#64) sourceBody281_297 sourceBody281_8

def sourceBody281_299 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_298 sourceBody281_5

def sourceBody281_300 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_299 sourceBody281_8

def sourceBody281_301 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_280 sourceBody281_300

def sourceBody281_302 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_279 sourceBody281_301

def sourceBody281_303 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_275 sourceBody281_302

def sourceBody281_304 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_274 sourceBody281_303

def sourceBody281_305 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_273 sourceBody281_304

def sourceBody281_306 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 2)

def sourceBody281_307 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 28)

def sourceBody281_308 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody281_8, 281, 22)) (some 273) ([24, 18]) (some (24, sourceBody281_254, 281, 23))

def sourceBody281_309 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_308 sourceBody281_5

def sourceBody281_310 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_309 sourceBody281_8

def sourceBody281_311 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_307 sourceBody281_310

def sourceBody281_312 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_306 sourceBody281_311

def sourceBody281_313 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_8 sourceBody281_312

def sourceBody281_314 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_8 sourceBody281_313

def sourceBody281_315 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_305 sourceBody281_314

def sourceBody281_316 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody281_317 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody281_8, 281, 24)) (some 79) ([12, 24, 18]) (some (12, sourceBody281_241, 281, 25))

def sourceBody281_318 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_317 sourceBody281_5

def sourceBody281_319 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_318 sourceBody281_8

def sourceBody281_320 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_266 sourceBody281_319

def sourceBody281_321 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_196 sourceBody281_320

def sourceBody281_322 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_316 sourceBody281_321

def sourceBody281_323 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_315 sourceBody281_322

def sourceBody281_324 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody281_8, 281, 26)) (some 70) ([24]) (some (24, sourceBody281_254, 281, 27))

def sourceBody281_325 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_324 sourceBody281_5

def sourceBody281_326 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_325 sourceBody281_8

def sourceBody281_327 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_281 sourceBody281_326

def sourceBody281_328 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_8 sourceBody281_327

def sourceBody281_329 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_8 sourceBody281_328

def sourceBody281_330 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_323 sourceBody281_329

def sourceBody281_331 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 30#64)

def sourceBody281_332 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_331 sourceBody281_291

def sourceBody281_333 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_8 sourceBody281_332

def sourceBody281_334 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_333 sourceBody281_295

def sourceBody281_335 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 32 (Flapjack.WordRegImm.imm 0#64) sourceBody281_334 sourceBody281_8

def sourceBody281_336 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_335 sourceBody281_5

def sourceBody281_337 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_336 sourceBody281_8

def sourceBody281_338 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_280 sourceBody281_337

def sourceBody281_339 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_279 sourceBody281_338

def sourceBody281_340 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_275 sourceBody281_339

def sourceBody281_341 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_274 sourceBody281_340

def sourceBody281_342 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_330 sourceBody281_341

def sourceBody281_343 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [12]

def sourceBody281_344 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_343 sourceBody281_8

def sourceBody281_345 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_192 sourceBody281_344

def sourceBody281_346 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_342 sourceBody281_345

def sourceBody281_347 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_245 sourceBody281_346

def sourceBody281_348 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_8 sourceBody281_347

def sourceBody281_349 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_8 sourceBody281_348

def sourceBody281_350 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_239 sourceBody281_349

def sourceBody281_351 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_8 sourceBody281_350

def sourceBody281_352 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_8 sourceBody281_351

def sourceBody281_353 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_235 sourceBody281_352

def sourceBody281_354 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_190 sourceBody281_353

def sourceBody281_355 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_8 sourceBody281_354

def sourceBody281_356 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_8 sourceBody281_355

def sourceBody281_357 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_178 sourceBody281_356

def sourceBody281_358 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_107 sourceBody281_357

def sourceBody281_359 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_8 sourceBody281_358

def sourceBody281_360 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_8 sourceBody281_359

def sourceBody281_361 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_87 sourceBody281_360

def sourceBody281_362 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_8 sourceBody281_361

def sourceBody281_363 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_8 sourceBody281_362

def sourceBody281_364 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_8 sourceBody281_363

def sourceBody281_365 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_8 sourceBody281_364

def sourceBody281_366 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_8 sourceBody281_365

def sourceBody281_367 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_8 sourceBody281_366

def sourceBody281_368 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_8 sourceBody281_367

def sourceBody281_369 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_8 sourceBody281_368

def sourceBody281_370 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_69 sourceBody281_369

def sourceBody281_371 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_31 sourceBody281_370

def sourceBody281_372 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_8 sourceBody281_371

def sourceBody281_373 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_8 sourceBody281_372

def sourceBody281_374 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody281_25 sourceBody281_373

def source281 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (281, 3, sourceBody281_374)
end InitECandidate.Proofs.WordStages
