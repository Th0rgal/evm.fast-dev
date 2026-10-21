import InitECandidate.Proofs.WordStages.Source767
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody783_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody783_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 2)

def sourceBody783_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 4)

def sourceBody783_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody783_4 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody783_0, 783, 2)) (some 723) ([10, 22]) (some (10, sourceBody783_3, 783, 3))

def sourceBody783_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody783_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody783_4 sourceBody783_5

def sourceBody783_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody783_6 sourceBody783_0

def sourceBody783_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody783_2 sourceBody783_7

def sourceBody783_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody783_1 sourceBody783_8

def sourceBody783_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 26)

def sourceBody783_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody783_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody783_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody783_14 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 22 (Flapjack.WordRegImm.reg 16) sourceBody783_12 sourceBody783_13

def sourceBody783_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody783_14 sourceBody783_5

def sourceBody783_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 22)

def sourceBody783_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody783_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [10]

def sourceBody783_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody783_18 sourceBody783_0

def sourceBody783_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody783_17 sourceBody783_19

def sourceBody783_21 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 30 (Flapjack.WordRegImm.imm 0#64) sourceBody783_20 sourceBody783_0

def sourceBody783_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody783_21 sourceBody783_5

def sourceBody783_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody783_22 sourceBody783_0

def sourceBody783_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody783_16 sourceBody783_23

def sourceBody783_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody783_15 sourceBody783_24

def sourceBody783_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody783_11 sourceBody783_25

def sourceBody783_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody783_10 sourceBody783_26

def sourceBody783_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 64#64])

def sourceBody783_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 48#64])

def sourceBody783_30 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody783_0, 783, 4)) (some 723) ([10, 22]) (some (10, sourceBody783_3, 783, 5))

def sourceBody783_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody783_30 sourceBody783_5

def sourceBody783_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody783_31 sourceBody783_0

def sourceBody783_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody783_29 sourceBody783_32

def sourceBody783_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody783_28 sourceBody783_33

def sourceBody783_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody783_27 sourceBody783_34

def sourceBody783_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody783_35 sourceBody783_27

def sourceBody783_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 128#64])

def sourceBody783_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 96#64])

def sourceBody783_39 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody783_0, 783, 6)) (some 723) ([10, 22]) (some (10, sourceBody783_3, 783, 7))

def sourceBody783_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody783_39 sourceBody783_5

def sourceBody783_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody783_40 sourceBody783_0

def sourceBody783_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody783_38 sourceBody783_41

def sourceBody783_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody783_37 sourceBody783_42

def sourceBody783_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody783_36 sourceBody783_43

def sourceBody783_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody783_44 sourceBody783_27

def sourceBody783_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 192#64])

def sourceBody783_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 96#64, Flapjack.WordLangExpHOL.const 48#64])

def sourceBody783_48 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody783_0, 783, 8)) (some 723) ([10, 22]) (some (10, sourceBody783_3, 783, 9))

def sourceBody783_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody783_48 sourceBody783_5

def sourceBody783_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody783_49 sourceBody783_0

def sourceBody783_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody783_47 sourceBody783_50

def sourceBody783_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody783_46 sourceBody783_51

def sourceBody783_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody783_45 sourceBody783_52

def sourceBody783_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody783_53 sourceBody783_27

def sourceBody783_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 22

def sourceBody783_56 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody783_0, 783, 10)) (some 728) ([22]) (some (22, sourceBody783_55, 783, 11))

def sourceBody783_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody783_56 sourceBody783_5

def sourceBody783_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody783_57 sourceBody783_0

def sourceBody783_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody783_2 sourceBody783_58

def sourceBody783_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 96#64])

def sourceBody783_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody783_62 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody783_0, 783, 12)) (some 728) ([16]) (some (16, sourceBody783_61, 783, 13))

def sourceBody783_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody783_62 sourceBody783_5

def sourceBody783_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody783_63 sourceBody783_0

def sourceBody783_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody783_60 sourceBody783_64

def sourceBody783_66 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 10)

def sourceBody783_67 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody783_68 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody783_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody783_70 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 30 (Flapjack.WordRegImm.reg 8) sourceBody783_68 sourceBody783_69

def sourceBody783_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody783_70 sourceBody783_5

def sourceBody783_72 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody783_73 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 30)

def sourceBody783_74 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody783_75 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.WordRegImm.reg 28) sourceBody783_74 sourceBody783_72

def sourceBody783_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody783_75 sourceBody783_5

def sourceBody783_77 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 22)

def sourceBody783_78 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody783_79 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody783_80 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody783_81 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 24 (Flapjack.WordRegImm.reg 18) sourceBody783_79 sourceBody783_80

def sourceBody783_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody783_81 sourceBody783_5

def sourceBody783_83 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody783_84 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 24)

def sourceBody783_85 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody783_86 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.WordRegImm.reg 20) sourceBody783_85 sourceBody783_83

def sourceBody783_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody783_86 sourceBody783_5

def sourceBody783_88 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.var 6])

def sourceBody783_89 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 192#64])

def sourceBody783_90 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 30

def sourceBody783_91 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody783_0, 783, 14)) (some 726) ([30]) (some (30, sourceBody783_90, 783, 15))

def sourceBody783_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody783_91 sourceBody783_5

def sourceBody783_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody783_92 sourceBody783_0

def sourceBody783_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody783_89 sourceBody783_93

def sourceBody783_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody783_0 sourceBody783_94

def sourceBody783_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody783_0 sourceBody783_95

def sourceBody783_97 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody783_98 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [16]

def sourceBody783_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody783_98 sourceBody783_0

def sourceBody783_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody783_97 sourceBody783_99

def sourceBody783_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody783_96 sourceBody783_100

def sourceBody783_102 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.imm 0#64) sourceBody783_101 sourceBody783_0

def sourceBody783_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody783_102 sourceBody783_5

def sourceBody783_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody783_103 sourceBody783_0

def sourceBody783_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody783_88 sourceBody783_104

def sourceBody783_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody783_87 sourceBody783_105

def sourceBody783_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody783_84 sourceBody783_106

def sourceBody783_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody783_83 sourceBody783_107

def sourceBody783_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody783_82 sourceBody783_108

def sourceBody783_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody783_78 sourceBody783_109

def sourceBody783_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody783_77 sourceBody783_110

def sourceBody783_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody783_76 sourceBody783_111

def sourceBody783_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody783_73 sourceBody783_112

def sourceBody783_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody783_72 sourceBody783_113

def sourceBody783_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody783_71 sourceBody783_114

def sourceBody783_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody783_67 sourceBody783_115

def sourceBody783_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody783_66 sourceBody783_116

def sourceBody783_118 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody783_0, 783, 16)) (some 727) ([30]) (some (30, sourceBody783_90, 783, 17))

def sourceBody783_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody783_118 sourceBody783_5

def sourceBody783_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody783_119 sourceBody783_0

def sourceBody783_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody783_89 sourceBody783_120

def sourceBody783_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody783_0 sourceBody783_121

def sourceBody783_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody783_0 sourceBody783_122

def sourceBody783_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody783_117 sourceBody783_123

def sourceBody783_125 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 4)

def sourceBody783_126 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 96#64])

def sourceBody783_127 : WordLangProgHOL (BitVec 64) :=
.call (none) (some 782) ([0, 16, 30]) (none)

def sourceBody783_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody783_127 sourceBody783_0

def sourceBody783_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody783_126 sourceBody783_128

def sourceBody783_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody783_125 sourceBody783_129

def sourceBody783_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody783_124 sourceBody783_130

def sourceBody783_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody783_65 sourceBody783_131

def sourceBody783_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody783_0 sourceBody783_132

def sourceBody783_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody783_0 sourceBody783_133

def sourceBody783_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody783_59 sourceBody783_134

def sourceBody783_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody783_0 sourceBody783_135

def sourceBody783_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody783_0 sourceBody783_136

def sourceBody783_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody783_54 sourceBody783_137

def sourceBody783_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody783_9 sourceBody783_138

def sourceBody783_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody783_0 sourceBody783_139

def sourceBody783_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody783_0 sourceBody783_140

def source783 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (783, 3, sourceBody783_141)
end InitECandidate.Proofs.WordStages
