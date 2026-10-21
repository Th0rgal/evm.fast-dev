import InitECandidate.Proofs.WordStages.Source304
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody320_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody320_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 32

def sourceBody320_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln, Flapjack.Spt.ln)), sourceBody320_0, 320, 2)) (some 75) ([]) (some (32, sourceBody320_1, 320, 3))

def sourceBody320_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody320_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_2 sourceBody320_3

def sourceBody320_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_4 sourceBody320_0

def sourceBody320_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 48#64)

def sourceBody320_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody320_8 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody320_0, 320, 4)) (some 74) ([6]) (some (6, sourceBody320_7, 320, 5))

def sourceBody320_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_8 sourceBody320_3

def sourceBody320_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_9 sourceBody320_0

def sourceBody320_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_6 sourceBody320_10

def sourceBody320_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 32, Flapjack.WordLangExpHOL.const 0#64])

def sourceBody320_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody320_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 28)

def sourceBody320_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 6) 18

def sourceBody320_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_15 sourceBody320_0

def sourceBody320_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_14 sourceBody320_16

def sourceBody320_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_17 sourceBody320_0

def sourceBody320_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_13 sourceBody320_18

def sourceBody320_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_0 sourceBody320_19

def sourceBody320_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_12 sourceBody320_20

def sourceBody320_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_0 sourceBody320_21

def sourceBody320_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 32, Flapjack.WordLangExpHOL.const 8#64])

def sourceBody320_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 2)

def sourceBody320_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_24 sourceBody320_18

def sourceBody320_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_0 sourceBody320_25

def sourceBody320_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_23 sourceBody320_26

def sourceBody320_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_0 sourceBody320_27

def sourceBody320_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_22 sourceBody320_28

def sourceBody320_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 32, Flapjack.WordLangExpHOL.const 16#64])

def sourceBody320_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_30 sourceBody320_20

def sourceBody320_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_0 sourceBody320_31

def sourceBody320_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_29 sourceBody320_32

def sourceBody320_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 32)

def sourceBody320_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 2)

def sourceBody320_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 28

def sourceBody320_37 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody320_0, 320, 6)) (some 317) ([28, 18]) (some (28, sourceBody320_36, 320, 7))

def sourceBody320_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_37 sourceBody320_3

def sourceBody320_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_38 sourceBody320_0

def sourceBody320_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_35 sourceBody320_39

def sourceBody320_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_34 sourceBody320_40

def sourceBody320_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_0 sourceBody320_41

def sourceBody320_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_0 sourceBody320_42

def sourceBody320_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_33 sourceBody320_43

def sourceBody320_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 32)

def sourceBody320_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 6)

def sourceBody320_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody320_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody320_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody320_50 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 18 (Flapjack.WordRegImm.reg 36) sourceBody320_48 sourceBody320_49

def sourceBody320_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_50 sourceBody320_3

def sourceBody320_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 18)

def sourceBody320_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody320_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 28, Flapjack.WordLangExpHOL.const 0#64]))

def sourceBody320_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody320_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 18)

def sourceBody320_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 2#64)

def sourceBody320_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody320_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody320_60 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 16 (Flapjack.WordRegImm.reg 34) sourceBody320_58 sourceBody320_59

def sourceBody320_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_60 sourceBody320_3

def sourceBody320_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 16)

def sourceBody320_63 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody320_64 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody320_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 16#64])

def sourceBody320_66 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 16)

def sourceBody320_67 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 26) 34

def sourceBody320_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_67 sourceBody320_0

def sourceBody320_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_66 sourceBody320_68

def sourceBody320_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_69 sourceBody320_0

def sourceBody320_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_58 sourceBody320_70

def sourceBody320_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_0 sourceBody320_71

def sourceBody320_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_65 sourceBody320_72

def sourceBody320_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_0 sourceBody320_73

def sourceBody320_75 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 28, Flapjack.WordLangExpHOL.const 48#64]))

def sourceBody320_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_75 sourceBody320_0

def sourceBody320_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_76 sourceBody320_0

def sourceBody320_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_74 sourceBody320_77

def sourceBody320_79 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 36)

def sourceBody320_80 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 26

def sourceBody320_81 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody320_0, 320, 8)) (some 319) ([26]) (some (26, sourceBody320_80, 320, 9))

def sourceBody320_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_81 sourceBody320_3

def sourceBody320_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_82 sourceBody320_0

def sourceBody320_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_79 sourceBody320_83

def sourceBody320_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_78 sourceBody320_84

def sourceBody320_86 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.imm 0#64) sourceBody320_85 sourceBody320_0

def sourceBody320_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_86 sourceBody320_3

def sourceBody320_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_87 sourceBody320_0

def sourceBody320_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_62 sourceBody320_88

def sourceBody320_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_61 sourceBody320_89

def sourceBody320_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_64 sourceBody320_90

def sourceBody320_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_63 sourceBody320_91

def sourceBody320_93 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 3#64)

def sourceBody320_94 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody320_95 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 26)

def sourceBody320_96 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 16#64)

def sourceBody320_97 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody320_98 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.less) 34 (Flapjack.WordRegImm.reg 10) sourceBody320_97 sourceBody320_64

def sourceBody320_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_98 sourceBody320_3

def sourceBody320_100 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody320_101 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 34)

def sourceBody320_102 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody320_103 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 22 (Flapjack.WordRegImm.reg 38) sourceBody320_102 sourceBody320_100

def sourceBody320_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_103 sourceBody320_3

def sourceBody320_105 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 4)

def sourceBody320_106 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody320_107 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody320_108 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody320_109 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 24 (Flapjack.WordRegImm.reg 14) sourceBody320_107 sourceBody320_108

def sourceBody320_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_109 sourceBody320_3

def sourceBody320_111 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody320_112 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 24)

def sourceBody320_113 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody320_114 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.WordRegImm.reg 30) sourceBody320_113 sourceBody320_111

def sourceBody320_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_114 sourceBody320_3

def sourceBody320_116 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and [Flapjack.WordLangExpHOL.var 22, Flapjack.WordLangExpHOL.var 8])

def sourceBody320_117 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 28, Flapjack.WordLangExpHOL.const 32#64,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 26)
          (Flapjack.WordLangExpHOL.const 3#64)]))

def sourceBody320_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_117 sourceBody320_0

def sourceBody320_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_118 sourceBody320_0

def sourceBody320_120 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 26, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody320_121 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 16)

def sourceBody320_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_121 sourceBody320_0

def sourceBody320_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_122 sourceBody320_0

def sourceBody320_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_120 sourceBody320_123

def sourceBody320_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_0 sourceBody320_124

def sourceBody320_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_119 sourceBody320_125

def sourceBody320_127 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 36)

def sourceBody320_128 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody320_129 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody320_0, 320, 10)) (some 319) ([16]) (some (16, sourceBody320_128, 320, 11))

def sourceBody320_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_129 sourceBody320_3

def sourceBody320_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_130 sourceBody320_0

def sourceBody320_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_127 sourceBody320_131

def sourceBody320_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_126 sourceBody320_132

def sourceBody320_134 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody320_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_133 sourceBody320_134

def sourceBody320_136 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody320_137 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 20 (Flapjack.WordRegImm.imm 0#64) sourceBody320_135 sourceBody320_136

def sourceBody320_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_137 sourceBody320_3

def sourceBody320_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_138 sourceBody320_0

def sourceBody320_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_116 sourceBody320_139

def sourceBody320_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_115 sourceBody320_140

def sourceBody320_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_112 sourceBody320_141

def sourceBody320_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_111 sourceBody320_142

def sourceBody320_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_110 sourceBody320_143

def sourceBody320_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_106 sourceBody320_144

def sourceBody320_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_105 sourceBody320_145

def sourceBody320_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_104 sourceBody320_146

def sourceBody320_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_101 sourceBody320_147

def sourceBody320_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_100 sourceBody320_148

def sourceBody320_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_99 sourceBody320_149

def sourceBody320_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_96 sourceBody320_150

def sourceBody320_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_95 sourceBody320_151

def sourceBody320_153 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
  PUnit.unit Flapjack.Spt.ln) sourceBody320_152 (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
    PUnit.unit
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody320_154 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_153 sourceBody320_3

def sourceBody320_155 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_3 sourceBody320_154

def sourceBody320_156 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 16#64])

def sourceBody320_157 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 34)

def sourceBody320_158 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 16) 10

def sourceBody320_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_158 sourceBody320_0

def sourceBody320_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_157 sourceBody320_159

def sourceBody320_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_160 sourceBody320_0

def sourceBody320_162 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_95 sourceBody320_161

def sourceBody320_163 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_0 sourceBody320_162

def sourceBody320_164 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_156 sourceBody320_163

def sourceBody320_165 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_0 sourceBody320_164

def sourceBody320_166 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_155 sourceBody320_165

def sourceBody320_167 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_94 sourceBody320_166

def sourceBody320_168 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_0 sourceBody320_167

def sourceBody320_169 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.imm 0#64) sourceBody320_168 sourceBody320_0

def sourceBody320_170 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_169 sourceBody320_3

def sourceBody320_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_170 sourceBody320_0

def sourceBody320_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_62 sourceBody320_171

def sourceBody320_173 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_61 sourceBody320_172

def sourceBody320_174 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_93 sourceBody320_173

def sourceBody320_175 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_56 sourceBody320_174

def sourceBody320_176 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.imm 0#64) sourceBody320_92 sourceBody320_175

def sourceBody320_177 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_176 sourceBody320_3

def sourceBody320_178 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_177 sourceBody320_0

def sourceBody320_179 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_62 sourceBody320_178

def sourceBody320_180 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_61 sourceBody320_179

def sourceBody320_181 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_57 sourceBody320_180

def sourceBody320_182 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_56 sourceBody320_181

def sourceBody320_183 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 4)

def sourceBody320_184 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 16 (Flapjack.WordRegImm.reg 34) sourceBody320_58 sourceBody320_59

def sourceBody320_185 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_184 sourceBody320_3

def sourceBody320_186 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 48#64)

def sourceBody320_187 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody320_0, 320, 12)) (some 74) ([16]) (some (16, sourceBody320_128, 320, 13))

def sourceBody320_188 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_187 sourceBody320_3

def sourceBody320_189 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_188 sourceBody320_0

def sourceBody320_190 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_186 sourceBody320_189

def sourceBody320_191 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 26, Flapjack.WordLangExpHOL.const 0#64])

def sourceBody320_192 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 6)

def sourceBody320_193 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_192 sourceBody320_161

def sourceBody320_194 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_0 sourceBody320_193

def sourceBody320_195 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_191 sourceBody320_194

def sourceBody320_196 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_0 sourceBody320_195

def sourceBody320_197 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 26, Flapjack.WordLangExpHOL.const 8#64])

def sourceBody320_198 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 36)

def sourceBody320_199 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_198 sourceBody320_161

def sourceBody320_200 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_0 sourceBody320_199

def sourceBody320_201 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_197 sourceBody320_200

def sourceBody320_202 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_0 sourceBody320_201

def sourceBody320_203 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_196 sourceBody320_202

def sourceBody320_204 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 26, Flapjack.WordLangExpHOL.const 16#64])

def sourceBody320_205 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_64 sourceBody320_161

def sourceBody320_206 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_0 sourceBody320_205

def sourceBody320_207 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_204 sourceBody320_206

def sourceBody320_208 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_0 sourceBody320_207

def sourceBody320_209 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_203 sourceBody320_208

def sourceBody320_210 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 36)

def sourceBody320_211 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 34

def sourceBody320_212 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody320_0, 320, 14)) (some 317) ([34, 10]) (some (34, sourceBody320_211, 320, 15))

def sourceBody320_213 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_212 sourceBody320_3

def sourceBody320_214 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_213 sourceBody320_0

def sourceBody320_215 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_210 sourceBody320_214

def sourceBody320_216 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_95 sourceBody320_215

def sourceBody320_217 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_0 sourceBody320_216

def sourceBody320_218 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_0 sourceBody320_217

def sourceBody320_219 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_209 sourceBody320_218

def sourceBody320_220 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 26)

def sourceBody320_221 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_220 sourceBody320_0

def sourceBody320_222 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_221 sourceBody320_0

def sourceBody320_223 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_219 sourceBody320_222

def sourceBody320_224 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_190 sourceBody320_223

def sourceBody320_225 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_0 sourceBody320_224

def sourceBody320_226 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_0 sourceBody320_225

def sourceBody320_227 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 6)

def sourceBody320_228 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 28)

def sourceBody320_229 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody320_0, 320, 16)) (some 318) ([16, 34]) (some (16, sourceBody320_128, 320, 17))

def sourceBody320_230 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_229 sourceBody320_3

def sourceBody320_231 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_230 sourceBody320_0

def sourceBody320_232 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_228 sourceBody320_231

def sourceBody320_233 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_227 sourceBody320_232

def sourceBody320_234 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_0 sourceBody320_233

def sourceBody320_235 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_0 sourceBody320_234

def sourceBody320_236 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 0#64]))

def sourceBody320_237 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_236 sourceBody320_222

def sourceBody320_238 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_0 sourceBody320_237

def sourceBody320_239 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_235 sourceBody320_238

def sourceBody320_240 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.imm 0#64) sourceBody320_226 sourceBody320_239

def sourceBody320_241 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_240 sourceBody320_3

def sourceBody320_242 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_241 sourceBody320_0

def sourceBody320_243 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_62 sourceBody320_242

def sourceBody320_244 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_185 sourceBody320_243

def sourceBody320_245 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_64 sourceBody320_244

def sourceBody320_246 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_183 sourceBody320_245

def sourceBody320_247 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_182 sourceBody320_246

def sourceBody320_248 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_55 sourceBody320_247

def sourceBody320_249 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_0 sourceBody320_248

def sourceBody320_250 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_47 sourceBody320_249

def sourceBody320_251 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_0 sourceBody320_250

def sourceBody320_252 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_54 sourceBody320_251

def sourceBody320_253 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_0 sourceBody320_252

def sourceBody320_254 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_53 sourceBody320_253

def sourceBody320_255 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_0 sourceBody320_254

def sourceBody320_256 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_255 sourceBody320_134

def sourceBody320_257 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 4 (Flapjack.WordRegImm.imm 0#64) sourceBody320_256 sourceBody320_136

def sourceBody320_258 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_257 sourceBody320_3

def sourceBody320_259 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_258 sourceBody320_0

def sourceBody320_260 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_52 sourceBody320_259

def sourceBody320_261 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_51 sourceBody320_260

def sourceBody320_262 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_47 sourceBody320_261

def sourceBody320_263 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_46 sourceBody320_262

def sourceBody320_264 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
  PUnit.unit Flapjack.Spt.ln) sourceBody320_263 (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody320_265 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_264 sourceBody320_3

def sourceBody320_266 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_3 sourceBody320_265

def sourceBody320_267 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 12)

def sourceBody320_268 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody320_269 : WordLangProgHOL (BitVec 64) :=
.call (some (([28]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody320_0, 320, 18)) (some 76) ([18]) (some (18, sourceBody320_268, 320, 19))

def sourceBody320_270 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_269 sourceBody320_3

def sourceBody320_271 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_270 sourceBody320_0

def sourceBody320_272 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_267 sourceBody320_271

def sourceBody320_273 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_0 sourceBody320_272

def sourceBody320_274 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_0 sourceBody320_273

def sourceBody320_275 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_266 sourceBody320_274

def sourceBody320_276 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [28]

def sourceBody320_277 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_276 sourceBody320_0

def sourceBody320_278 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_13 sourceBody320_277

def sourceBody320_279 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_275 sourceBody320_278

def sourceBody320_280 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_45 sourceBody320_279

def sourceBody320_281 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_0 sourceBody320_280

def sourceBody320_282 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_44 sourceBody320_281

def sourceBody320_283 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_11 sourceBody320_282

def sourceBody320_284 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_0 sourceBody320_283

def sourceBody320_285 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_0 sourceBody320_284

def sourceBody320_286 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_5 sourceBody320_285

def sourceBody320_287 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_0 sourceBody320_286

def sourceBody320_288 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody320_0 sourceBody320_287

def source320 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (320, 2, sourceBody320_288)
end InitECandidate.Proofs.WordStages
