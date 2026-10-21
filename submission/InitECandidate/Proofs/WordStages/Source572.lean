import InitECandidate.Proofs.WordStages.Source556
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody572_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody572_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody572_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([12, 32, 6, 26]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody572_0, 572, 2)) (some 471) ([]) (some (18, sourceBody572_1, 572, 3))

def sourceBody572_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody572_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_2 sourceBody572_3

def sourceBody572_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_4 sourceBody572_0

def sourceBody572_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.const 20#64)

def sourceBody572_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 38

def sourceBody572_8 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody572_0, 572, 4)) (some 466) ([38]) (some (38, sourceBody572_7, 572, 5))

def sourceBody572_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_8 sourceBody572_3

def sourceBody572_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_9 sourceBody572_0

def sourceBody572_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_6 sourceBody572_10

def sourceBody572_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_0 sourceBody572_11

def sourceBody572_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_0 sourceBody572_12

def sourceBody572_14 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody572_0, 572, 6)) (some 568) ([]) (some (38, sourceBody572_7, 572, 7))

def sourceBody572_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_14 sourceBody572_3

def sourceBody572_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_15 sourceBody572_0

def sourceBody572_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 40#64]))

def sourceBody572_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 12)

def sourceBody572_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 32)

def sourceBody572_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 6)

def sourceBody572_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 26)

def sourceBody572_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 24

def sourceBody572_23 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody572_0, 572, 8)) (some 458) ([24, 16, 36, 10]) (some (24, sourceBody572_22, 572, 9))

def sourceBody572_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_23 sourceBody572_3

def sourceBody572_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_24 sourceBody572_0

def sourceBody572_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_21 sourceBody572_25

def sourceBody572_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_20 sourceBody572_26

def sourceBody572_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_19 sourceBody572_27

def sourceBody572_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_18 sourceBody572_28

def sourceBody572_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 4)

def sourceBody572_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 38)

def sourceBody572_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody572_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody572_34 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notLower) 16 (Flapjack.WordRegImm.reg 36) sourceBody572_32 sourceBody572_33

def sourceBody572_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_34 sourceBody572_3

def sourceBody572_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 256#64])

def sourceBody572_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 38)

def sourceBody572_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody572_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody572_40 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 30 (Flapjack.WordRegImm.reg 20) sourceBody572_38 sourceBody572_39

def sourceBody572_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_40 sourceBody572_3

def sourceBody572_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 4)

def sourceBody572_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 18446744073709551615#64)

def sourceBody572_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody572_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody572_46 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 2 (Flapjack.WordRegImm.reg 22) sourceBody572_44 sourceBody572_45

def sourceBody572_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_46 sourceBody572_3

def sourceBody572_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody572_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.or
    [Flapjack.WordLangExpHOL.var 16, Flapjack.WordLangExpHOL.var 30, Flapjack.WordLangExpHOL.var 2])

def sourceBody572_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody572_51 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 34 (Flapjack.WordRegImm.reg 8) sourceBody572_50 sourceBody572_48

def sourceBody572_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_51 sourceBody572_3

def sourceBody572_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 34)

def sourceBody572_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody572_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody572_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody572_57 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody572_0, 572, 10)) (some 472) ([16, 36, 10, 30]) (some (16, sourceBody572_56, 572, 11))

def sourceBody572_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_57 sourceBody572_3

def sourceBody572_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_58 sourceBody572_0

def sourceBody572_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_39 sourceBody572_59

def sourceBody572_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_55 sourceBody572_60

def sourceBody572_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_54 sourceBody572_61

def sourceBody572_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_33 sourceBody572_62

def sourceBody572_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_0 sourceBody572_63

def sourceBody572_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_0 sourceBody572_64

def sourceBody572_66 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody572_0, 572, 12)) (some 486) ([16]) (some (16, sourceBody572_56, 572, 13))

def sourceBody572_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_66 sourceBody572_3

def sourceBody572_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_67 sourceBody572_0

def sourceBody572_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_32 sourceBody572_68

def sourceBody572_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_0 sourceBody572_69

def sourceBody572_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_0 sourceBody572_70

def sourceBody572_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_65 sourceBody572_71

def sourceBody572_73 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody572_74 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [24]

def sourceBody572_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_74 sourceBody572_0

def sourceBody572_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_73 sourceBody572_75

def sourceBody572_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_72 sourceBody572_76

def sourceBody572_78 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 28 (Flapjack.WordRegImm.imm 0#64) sourceBody572_77 sourceBody572_0

def sourceBody572_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_78 sourceBody572_3

def sourceBody572_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_79 sourceBody572_0

def sourceBody572_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_53 sourceBody572_80

def sourceBody572_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_52 sourceBody572_81

def sourceBody572_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_49 sourceBody572_82

def sourceBody572_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_48 sourceBody572_83

def sourceBody572_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_47 sourceBody572_84

def sourceBody572_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_43 sourceBody572_85

def sourceBody572_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_42 sourceBody572_86

def sourceBody572_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_41 sourceBody572_87

def sourceBody572_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_37 sourceBody572_88

def sourceBody572_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_36 sourceBody572_89

def sourceBody572_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_35 sourceBody572_90

def sourceBody572_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_31 sourceBody572_91

def sourceBody572_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_30 sourceBody572_92

def sourceBody572_94 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 38, Flapjack.WordLangExpHOL.var 4])

def sourceBody572_95 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody572_96 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 16)

def sourceBody572_97 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 24)

def sourceBody572_98 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody572_99 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 10 (Flapjack.WordRegImm.reg 30) sourceBody572_98 sourceBody572_55

def sourceBody572_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_99 sourceBody572_3

def sourceBody572_101 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 10)

def sourceBody572_102 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.const 50#64)

def sourceBody572_103 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 36)

def sourceBody572_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_103 sourceBody572_0

def sourceBody572_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_104 sourceBody572_0

def sourceBody572_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_102 sourceBody572_105

def sourceBody572_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_0 sourceBody572_106

def sourceBody572_108 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.const 4#64)

def sourceBody572_109 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 36

def sourceBody572_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_108 sourceBody572_109

def sourceBody572_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_107 sourceBody572_110

def sourceBody572_112 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 20 (Flapjack.WordRegImm.imm 0#64) sourceBody572_111 sourceBody572_0

def sourceBody572_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_112 sourceBody572_3

def sourceBody572_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_113 sourceBody572_0

def sourceBody572_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_101 sourceBody572_114

def sourceBody572_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_100 sourceBody572_115

def sourceBody572_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_97 sourceBody572_116

def sourceBody572_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_96 sourceBody572_117

def sourceBody572_119 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 16#64]),
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 16, Flapjack.WordLangExpHOL.var 24])
        (Flapjack.WordLangExpHOL.const 5#64)])

def sourceBody572_120 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody572_121 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 40

def sourceBody572_122 : WordLangProgHOL (BitVec 64) :=
.call (some (([36, 10, 30, 20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody572_0, 572, 14)) (some 146) ([40, 2]) (some (40, sourceBody572_121, 572, 15))

def sourceBody572_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_122 sourceBody572_3

def sourceBody572_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_123 sourceBody572_0

def sourceBody572_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_120 sourceBody572_124

def sourceBody572_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_119 sourceBody572_125

def sourceBody572_127 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 24)

def sourceBody572_128 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 2

def sourceBody572_129 : WordLangProgHOL (BitVec 64) :=
.call (some (([40]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody572_0, 572, 16)) (some 430) ([2]) (some (2, sourceBody572_128, 572, 17))

def sourceBody572_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_129 sourceBody572_3

def sourceBody572_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_130 sourceBody572_0

def sourceBody572_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_127 sourceBody572_131

def sourceBody572_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_0 sourceBody572_132

def sourceBody572_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_0 sourceBody572_133

def sourceBody572_135 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 36)

def sourceBody572_136 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 10)

def sourceBody572_137 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 30)

def sourceBody572_138 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 20)

def sourceBody572_139 : WordLangProgHOL (BitVec 64) :=
.call (some (([40]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody572_0, 572, 18)) (some 472) ([2, 22, 14, 34]) (some (2, sourceBody572_128, 572, 19))

def sourceBody572_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_139 sourceBody572_3

def sourceBody572_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_140 sourceBody572_0

def sourceBody572_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_138 sourceBody572_141

def sourceBody572_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_137 sourceBody572_142

def sourceBody572_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_136 sourceBody572_143

def sourceBody572_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_135 sourceBody572_144

def sourceBody572_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_0 sourceBody572_145

def sourceBody572_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_0 sourceBody572_146

def sourceBody572_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_134 sourceBody572_147

def sourceBody572_149 : WordLangProgHOL (BitVec 64) :=
.call (some (([40]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody572_0, 572, 20)) (some 486) ([2]) (some (2, sourceBody572_128, 572, 21))

def sourceBody572_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_149 sourceBody572_3

def sourceBody572_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_150 sourceBody572_0

def sourceBody572_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_44 sourceBody572_151

def sourceBody572_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_0 sourceBody572_152

def sourceBody572_154 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_0 sourceBody572_153

def sourceBody572_155 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_148 sourceBody572_154

def sourceBody572_156 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody572_157 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [40]

def sourceBody572_158 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_157 sourceBody572_0

def sourceBody572_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_156 sourceBody572_158

def sourceBody572_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_155 sourceBody572_159

def sourceBody572_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_126 sourceBody572_160

def sourceBody572_162 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_0 sourceBody572_161

def sourceBody572_163 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_0 sourceBody572_162

def sourceBody572_164 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_0 sourceBody572_163

def sourceBody572_165 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_0 sourceBody572_164

def sourceBody572_166 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_0 sourceBody572_165

def sourceBody572_167 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_0 sourceBody572_166

def sourceBody572_168 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_0 sourceBody572_167

def sourceBody572_169 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_0 sourceBody572_168

def sourceBody572_170 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_118 sourceBody572_169

def sourceBody572_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_95 sourceBody572_170

def sourceBody572_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_0 sourceBody572_171

def sourceBody572_173 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_94 sourceBody572_172

def sourceBody572_174 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_0 sourceBody572_173

def sourceBody572_175 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_93 sourceBody572_174

def sourceBody572_176 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_29 sourceBody572_175

def sourceBody572_177 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_0 sourceBody572_176

def sourceBody572_178 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_0 sourceBody572_177

def sourceBody572_179 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_17 sourceBody572_178

def sourceBody572_180 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_0 sourceBody572_179

def sourceBody572_181 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_16 sourceBody572_180

def sourceBody572_182 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_0 sourceBody572_181

def sourceBody572_183 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_0 sourceBody572_182

def sourceBody572_184 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_13 sourceBody572_183

def sourceBody572_185 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_5 sourceBody572_184

def sourceBody572_186 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_0 sourceBody572_185

def sourceBody572_187 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_0 sourceBody572_186

def sourceBody572_188 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_0 sourceBody572_187

def sourceBody572_189 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_0 sourceBody572_188

def sourceBody572_190 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_0 sourceBody572_189

def sourceBody572_191 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_0 sourceBody572_190

def sourceBody572_192 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_0 sourceBody572_191

def sourceBody572_193 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody572_0 sourceBody572_192

def source572 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (572, 1, sourceBody572_193)
end InitECandidate.Proofs.WordStages
