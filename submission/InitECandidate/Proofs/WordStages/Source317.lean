import InitECandidate.Proofs.WordStages.Source301
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody317_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody317_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 0#64]))

def sourceBody317_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody317_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody317_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody317_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 22)

def sourceBody317_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 3#64)

def sourceBody317_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody317_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody317_9 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.WordRegImm.reg 16) sourceBody317_7 sourceBody317_8

def sourceBody317_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody317_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_9 sourceBody317_10

def sourceBody317_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 6)

def sourceBody317_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 40#64]))

def sourceBody317_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr (Flapjack.WordLangExpHOL.var 26)
        (Flapjack.WordLangExpHOL.const 1#64),
      Flapjack.WordLangExpHOL.const 2#64])

def sourceBody317_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody317_16 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody317_0, 317, 2)) (some 68) ([6]) (some (6, sourceBody317_15, 317, 3))

def sourceBody317_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_16 sourceBody317_10

def sourceBody317_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_17 sourceBody317_0

def sourceBody317_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_14 sourceBody317_18

def sourceBody317_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 22)

def sourceBody317_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody317_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody317_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody317_24 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 12 (Flapjack.WordRegImm.reg 24) sourceBody317_22 sourceBody317_23

def sourceBody317_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_24 sourceBody317_10

def sourceBody317_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 12)

def sourceBody317_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_7 sourceBody317_0

def sourceBody317_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_27 sourceBody317_0

def sourceBody317_29 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.imm 0#64) sourceBody317_28 sourceBody317_0

def sourceBody317_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_29 sourceBody317_10

def sourceBody317_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_30 sourceBody317_0

def sourceBody317_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_26 sourceBody317_31

def sourceBody317_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_25 sourceBody317_32

def sourceBody317_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_21 sourceBody317_33

def sourceBody317_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_20 sourceBody317_34

def sourceBody317_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 32#64]))

def sourceBody317_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 26)

def sourceBody317_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 6)

def sourceBody317_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 18)

def sourceBody317_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody317_41 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody317_0, 317, 4)) (some 286) ([16, 12, 24, 10]) (some (16, sourceBody317_40, 317, 5))

def sourceBody317_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_41 sourceBody317_10

def sourceBody317_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_42 sourceBody317_0

def sourceBody317_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_39 sourceBody317_43

def sourceBody317_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_38 sourceBody317_44

def sourceBody317_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_37 sourceBody317_45

def sourceBody317_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_36 sourceBody317_46

def sourceBody317_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_35 sourceBody317_47

def sourceBody317_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 18)

def sourceBody317_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 12 (Flapjack.WordLangAddr.addr 12 0#64))

def sourceBody317_51 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 12)

def sourceBody317_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 14)

def sourceBody317_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody317_54 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody317_0, 317, 6)) (some 179) ([24, 10]) (some (12, sourceBody317_53, 317, 7))

def sourceBody317_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_54 sourceBody317_10

def sourceBody317_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_55 sourceBody317_0

def sourceBody317_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_52 sourceBody317_56

def sourceBody317_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_51 sourceBody317_57

def sourceBody317_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_50 sourceBody317_58

def sourceBody317_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_49 sourceBody317_59

def sourceBody317_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 16)

def sourceBody317_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_61 sourceBody317_0

def sourceBody317_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_62 sourceBody317_0

def sourceBody317_64 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 22)

def sourceBody317_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody317_66 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody317_67 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 24 (Flapjack.WordRegImm.reg 10) sourceBody317_21 sourceBody317_66

def sourceBody317_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_67 sourceBody317_10

def sourceBody317_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 24)

def sourceBody317_70 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 48#64]))

def sourceBody317_71 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 56#64]))

def sourceBody317_72 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 24

def sourceBody317_73 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody317_0, 317, 8)) (some 322) ([24, 10]) (some (24, sourceBody317_72, 317, 9))

def sourceBody317_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_73 sourceBody317_10

def sourceBody317_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_74 sourceBody317_0

def sourceBody317_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_71 sourceBody317_75

def sourceBody317_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_70 sourceBody317_76

def sourceBody317_78 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.var 12])

def sourceBody317_79 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 24)

def sourceBody317_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_79 sourceBody317_0

def sourceBody317_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_80 sourceBody317_0

def sourceBody317_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_78 sourceBody317_81

def sourceBody317_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_0 sourceBody317_82

def sourceBody317_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_77 sourceBody317_83

def sourceBody317_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_0 sourceBody317_84

def sourceBody317_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_0 sourceBody317_85

def sourceBody317_87 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 20 (Flapjack.WordRegImm.imm 0#64) sourceBody317_86 sourceBody317_0

def sourceBody317_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_87 sourceBody317_10

def sourceBody317_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_88 sourceBody317_0

def sourceBody317_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_69 sourceBody317_89

def sourceBody317_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_68 sourceBody317_90

def sourceBody317_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_65 sourceBody317_91

def sourceBody317_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_64 sourceBody317_92

def sourceBody317_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_63 sourceBody317_93

def sourceBody317_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_60 sourceBody317_94

def sourceBody317_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_0 sourceBody317_95

def sourceBody317_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_0 sourceBody317_96

def sourceBody317_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_48 sourceBody317_97

def sourceBody317_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_8 sourceBody317_98

def sourceBody317_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_0 sourceBody317_99

def sourceBody317_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_19 sourceBody317_100

def sourceBody317_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_13 sourceBody317_101

def sourceBody317_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_0 sourceBody317_102

def sourceBody317_104 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.imm 0#64) sourceBody317_103 sourceBody317_0

def sourceBody317_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_104 sourceBody317_10

def sourceBody317_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_105 sourceBody317_0

def sourceBody317_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_12 sourceBody317_106

def sourceBody317_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_11 sourceBody317_107

def sourceBody317_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_6 sourceBody317_108

def sourceBody317_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_5 sourceBody317_109

def sourceBody317_111 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 24#64])

def sourceBody317_112 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 18)

def sourceBody317_113 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 6)

def sourceBody317_114 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 26) 16

def sourceBody317_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_114 sourceBody317_0

def sourceBody317_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_113 sourceBody317_115

def sourceBody317_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_116 sourceBody317_0

def sourceBody317_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_112 sourceBody317_117

def sourceBody317_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_0 sourceBody317_118

def sourceBody317_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_111 sourceBody317_119

def sourceBody317_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_0 sourceBody317_120

def sourceBody317_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_110 sourceBody317_121

def sourceBody317_123 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 32#64])

def sourceBody317_124 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 14)

def sourceBody317_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_124 sourceBody317_117

def sourceBody317_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_0 sourceBody317_125

def sourceBody317_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_123 sourceBody317_126

def sourceBody317_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_0 sourceBody317_127

def sourceBody317_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_122 sourceBody317_128

def sourceBody317_130 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 40#64])

def sourceBody317_131 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 8)

def sourceBody317_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_131 sourceBody317_117

def sourceBody317_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_0 sourceBody317_132

def sourceBody317_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_130 sourceBody317_133

def sourceBody317_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_0 sourceBody317_134

def sourceBody317_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_129 sourceBody317_135

def sourceBody317_137 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody317_138 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [26]

def sourceBody317_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_138 sourceBody317_0

def sourceBody317_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_137 sourceBody317_139

def sourceBody317_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_136 sourceBody317_140

def sourceBody317_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_4 sourceBody317_141

def sourceBody317_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_0 sourceBody317_142

def sourceBody317_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_3 sourceBody317_143

def sourceBody317_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_0 sourceBody317_144

def sourceBody317_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_2 sourceBody317_145

def sourceBody317_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_0 sourceBody317_146

def sourceBody317_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_1 sourceBody317_147

def sourceBody317_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody317_0 sourceBody317_148

def source317 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (317, 3, sourceBody317_149)
end InitECandidate.Proofs.WordStages
