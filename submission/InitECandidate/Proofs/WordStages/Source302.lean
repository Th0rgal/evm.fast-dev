import InitECandidate.Proofs.WordStages.Source286
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody302_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody302_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody302_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody302_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 2)

def sourceBody302_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody302_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody302_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody302_7 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.WordRegImm.reg 22) sourceBody302_5 sourceBody302_6

def sourceBody302_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_7 sourceBody302_2

def sourceBody302_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 14)

def sourceBody302_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 0#64]))

def sourceBody302_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 18)

def sourceBody302_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody302_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody302_14 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 22 (Flapjack.WordRegImm.reg 8) sourceBody302_13 sourceBody302_4

def sourceBody302_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_14 sourceBody302_2

def sourceBody302_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 22)

def sourceBody302_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 2#64)

def sourceBody302_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 22

def sourceBody302_19 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody302_0, 302, 2)) (some 282) ([22]) (some (22, sourceBody302_18, 302, 3))

def sourceBody302_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_19 sourceBody302_2

def sourceBody302_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_20 sourceBody302_0

def sourceBody302_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_17 sourceBody302_21

def sourceBody302_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_0 sourceBody302_22

def sourceBody302_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_0 sourceBody302_23

def sourceBody302_25 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 16 (Flapjack.WordRegImm.imm 0#64) sourceBody302_24 sourceBody302_0

def sourceBody302_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_25 sourceBody302_2

def sourceBody302_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_26 sourceBody302_0

def sourceBody302_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_16 sourceBody302_27

def sourceBody302_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_15 sourceBody302_28

def sourceBody302_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_12 sourceBody302_29

def sourceBody302_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_11 sourceBody302_30

def sourceBody302_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody302_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 40#64]))

def sourceBody302_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.var 10])

def sourceBody302_35 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 8 (Flapjack.WordRegImm.reg 16) sourceBody302_32 sourceBody302_12

def sourceBody302_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_35 sourceBody302_2

def sourceBody302_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 8)

def sourceBody302_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 32#64]))

def sourceBody302_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.var 10])

def sourceBody302_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 14)

def sourceBody302_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody302_42 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln, Flapjack.Spt.ln)), sourceBody302_0, 302, 4)) (some 79) ([8, 16, 12]) (some (8, sourceBody302_41, 302, 5))

def sourceBody302_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_42 sourceBody302_2

def sourceBody302_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_43 sourceBody302_0

def sourceBody302_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_40 sourceBody302_44

def sourceBody302_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_39 sourceBody302_45

def sourceBody302_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_38 sourceBody302_46

def sourceBody302_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody302_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody302_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody302_51 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 16 (Flapjack.WordRegImm.reg 12) sourceBody302_49 sourceBody302_50

def sourceBody302_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_51 sourceBody302_2

def sourceBody302_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 16)

def sourceBody302_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 48#64]))

def sourceBody302_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 56#64]))

def sourceBody302_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [8, 16, 12]

def sourceBody302_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_56 sourceBody302_0

def sourceBody302_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_55 sourceBody302_57

def sourceBody302_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_54 sourceBody302_58

def sourceBody302_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_32 sourceBody302_59

def sourceBody302_61 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 20 (Flapjack.WordRegImm.imm 0#64) sourceBody302_60 sourceBody302_0

def sourceBody302_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_61 sourceBody302_2

def sourceBody302_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_62 sourceBody302_0

def sourceBody302_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_53 sourceBody302_63

def sourceBody302_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_52 sourceBody302_64

def sourceBody302_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_48 sourceBody302_65

def sourceBody302_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_16 sourceBody302_66

def sourceBody302_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_47 sourceBody302_67

def sourceBody302_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_0 sourceBody302_68

def sourceBody302_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_0 sourceBody302_69

def sourceBody302_71 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.imm 0#64) sourceBody302_70 sourceBody302_0

def sourceBody302_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_71 sourceBody302_2

def sourceBody302_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_72 sourceBody302_0

def sourceBody302_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_37 sourceBody302_73

def sourceBody302_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_36 sourceBody302_74

def sourceBody302_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_34 sourceBody302_75

def sourceBody302_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_9 sourceBody302_76

def sourceBody302_78 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [22, 8, 16]

def sourceBody302_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_78 sourceBody302_0

def sourceBody302_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_50 sourceBody302_79

def sourceBody302_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_12 sourceBody302_80

def sourceBody302_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_4 sourceBody302_81

def sourceBody302_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_77 sourceBody302_82

def sourceBody302_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_33 sourceBody302_83

def sourceBody302_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_0 sourceBody302_84

def sourceBody302_86 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 16 (Flapjack.WordRegImm.imm 0#64) sourceBody302_85 sourceBody302_0

def sourceBody302_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_86 sourceBody302_2

def sourceBody302_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_87 sourceBody302_0

def sourceBody302_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_16 sourceBody302_88

def sourceBody302_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_15 sourceBody302_89

def sourceBody302_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_32 sourceBody302_90

def sourceBody302_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_11 sourceBody302_91

def sourceBody302_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_31 sourceBody302_92

def sourceBody302_94 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 2#64)

def sourceBody302_95 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.var 10])

def sourceBody302_96 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 14)

def sourceBody302_97 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 8 (Flapjack.WordRegImm.reg 16) sourceBody302_32 sourceBody302_12

def sourceBody302_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_97 sourceBody302_2

def sourceBody302_99 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.imm 0#64) sourceBody302_82 sourceBody302_0

def sourceBody302_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_99 sourceBody302_2

def sourceBody302_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_100 sourceBody302_0

def sourceBody302_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_37 sourceBody302_101

def sourceBody302_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_98 sourceBody302_102

def sourceBody302_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_96 sourceBody302_103

def sourceBody302_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_95 sourceBody302_104

def sourceBody302_106 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody302_0, 302, 6)) (some 79) ([8, 16, 12]) (some (8, sourceBody302_41, 302, 7))

def sourceBody302_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_106 sourceBody302_2

def sourceBody302_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_107 sourceBody302_0

def sourceBody302_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_40 sourceBody302_108

def sourceBody302_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_39 sourceBody302_109

def sourceBody302_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_38 sourceBody302_110

def sourceBody302_112 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 16 (Flapjack.WordRegImm.reg 12) sourceBody302_49 sourceBody302_50

def sourceBody302_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_112 sourceBody302_2

def sourceBody302_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_48 sourceBody302_57

def sourceBody302_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_50 sourceBody302_114

def sourceBody302_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_12 sourceBody302_115

def sourceBody302_117 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 20 (Flapjack.WordRegImm.imm 0#64) sourceBody302_116 sourceBody302_0

def sourceBody302_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_117 sourceBody302_2

def sourceBody302_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_118 sourceBody302_0

def sourceBody302_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_53 sourceBody302_119

def sourceBody302_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_113 sourceBody302_120

def sourceBody302_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_48 sourceBody302_121

def sourceBody302_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_16 sourceBody302_122

def sourceBody302_124 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.var 14])

def sourceBody302_125 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 8)

def sourceBody302_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_125 sourceBody302_0

def sourceBody302_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_126 sourceBody302_0

def sourceBody302_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_124 sourceBody302_127

def sourceBody302_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_0 sourceBody302_128

def sourceBody302_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_123 sourceBody302_129

def sourceBody302_131 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 48#64]))

def sourceBody302_132 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 8)

def sourceBody302_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_132 sourceBody302_0

def sourceBody302_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_133 sourceBody302_0

def sourceBody302_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_131 sourceBody302_134

def sourceBody302_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_0 sourceBody302_135

def sourceBody302_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_130 sourceBody302_136

def sourceBody302_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_111 sourceBody302_137

def sourceBody302_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_0 sourceBody302_138

def sourceBody302_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_0 sourceBody302_139

def sourceBody302_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_105 sourceBody302_140

def sourceBody302_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_33 sourceBody302_141

def sourceBody302_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_0 sourceBody302_142

def sourceBody302_144 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 10)

def sourceBody302_145 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 6)

def sourceBody302_146 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 168#64]))

def sourceBody302_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_36 sourceBody302_102

def sourceBody302_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_50 sourceBody302_147

def sourceBody302_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_9 sourceBody302_148

def sourceBody302_150 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 160#64]))

def sourceBody302_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_96 sourceBody302_79

def sourceBody302_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_150 sourceBody302_151

def sourceBody302_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_13 sourceBody302_152

def sourceBody302_154 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_149 sourceBody302_153

def sourceBody302_155 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_146 sourceBody302_154

def sourceBody302_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_0 sourceBody302_155

def sourceBody302_157 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 16 (Flapjack.WordRegImm.imm 0#64) sourceBody302_156 sourceBody302_0

def sourceBody302_158 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_157 sourceBody302_2

def sourceBody302_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_158 sourceBody302_0

def sourceBody302_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_16 sourceBody302_159

def sourceBody302_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_15 sourceBody302_160

def sourceBody302_162 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_145 sourceBody302_161

def sourceBody302_163 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_144 sourceBody302_162

def sourceBody302_164 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.var 10])

def sourceBody302_165 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 14 (Flapjack.WordLangAddr.addr 14 0#64))

def sourceBody302_166 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_165 sourceBody302_0

def sourceBody302_167 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_164 sourceBody302_166

def sourceBody302_168 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 32#64,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 14)
          (Flapjack.WordLangExpHOL.const 3#64)]))

def sourceBody302_169 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 22)

def sourceBody302_170 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_169 sourceBody302_0

def sourceBody302_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_170 sourceBody302_0

def sourceBody302_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_168 sourceBody302_171

def sourceBody302_173 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_167 sourceBody302_172

def sourceBody302_174 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_163 sourceBody302_173

def sourceBody302_175 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody302_176 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 14)

def sourceBody302_177 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_176 sourceBody302_0

def sourceBody302_178 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_177 sourceBody302_0

def sourceBody302_179 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_175 sourceBody302_178

def sourceBody302_180 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_0 sourceBody302_179

def sourceBody302_181 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_174 sourceBody302_180

def sourceBody302_182 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 16 (Flapjack.WordRegImm.imm 0#64) sourceBody302_143 sourceBody302_181

def sourceBody302_183 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_182 sourceBody302_2

def sourceBody302_184 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_183 sourceBody302_0

def sourceBody302_185 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_16 sourceBody302_184

def sourceBody302_186 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_15 sourceBody302_185

def sourceBody302_187 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_94 sourceBody302_186

def sourceBody302_188 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_11 sourceBody302_187

def sourceBody302_189 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_93 sourceBody302_188

def sourceBody302_190 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_10 sourceBody302_189

def sourceBody302_191 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_0 sourceBody302_190

def sourceBody302_192 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody302_193 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_191 sourceBody302_192

def sourceBody302_194 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody302_195 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.WordRegImm.imm 0#64) sourceBody302_193 sourceBody302_194

def sourceBody302_196 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_195 sourceBody302_2

def sourceBody302_197 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_196 sourceBody302_0

def sourceBody302_198 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_9 sourceBody302_197

def sourceBody302_199 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_8 sourceBody302_198

def sourceBody302_200 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_4 sourceBody302_199

def sourceBody302_201 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_3 sourceBody302_200

def sourceBody302_202 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.ls PUnit.unit))
  PUnit.unit Flapjack.Spt.ln) sourceBody302_201 (Flapjack.Spt.ls PUnit.unit)

def sourceBody302_203 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_202 sourceBody302_2

def sourceBody302_204 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_2 sourceBody302_203

def sourceBody302_205 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody302_206 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [18, 14, 22]

def sourceBody302_207 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_206 sourceBody302_0

def sourceBody302_208 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_4 sourceBody302_207

def sourceBody302_209 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_6 sourceBody302_208

def sourceBody302_210 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_205 sourceBody302_209

def sourceBody302_211 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_204 sourceBody302_210

def sourceBody302_212 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_1 sourceBody302_211

def sourceBody302_213 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody302_0 sourceBody302_212

def source302 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (302, 4, sourceBody302_213)
end InitECandidate.Proofs.WordStages
