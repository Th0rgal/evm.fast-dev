import InitECandidate.Proofs.WordStages.Source707
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody723_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody723_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 2)

def sourceBody723_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.const 16#64)

def sourceBody723_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody723_4 : WordLangProgHOL (BitVec 64) :=
.call (some (([38]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody723_0, 723, 2)) (some 80) ([12, 32]) (some (12, sourceBody723_3, 723, 3))

def sourceBody723_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody723_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_4 sourceBody723_5

def sourceBody723_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_6 sourceBody723_0

def sourceBody723_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_2 sourceBody723_7

def sourceBody723_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_1 sourceBody723_8

def sourceBody723_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 38)

def sourceBody723_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody723_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody723_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody723_14 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 32 (Flapjack.WordRegImm.reg 22) sourceBody723_12 sourceBody723_13

def sourceBody723_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_14 sourceBody723_5

def sourceBody723_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 32)

def sourceBody723_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody723_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [12]

def sourceBody723_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_18 sourceBody723_0

def sourceBody723_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_17 sourceBody723_19

def sourceBody723_21 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 44 (Flapjack.WordRegImm.imm 0#64) sourceBody723_20 sourceBody723_0

def sourceBody723_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_21 sourceBody723_5

def sourceBody723_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_22 sourceBody723_0

def sourceBody723_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_16 sourceBody723_23

def sourceBody723_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_15 sourceBody723_24

def sourceBody723_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_11 sourceBody723_25

def sourceBody723_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_10 sourceBody723_26

def sourceBody723_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 16#64])

def sourceBody723_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody723_30 : WordLangProgHOL (BitVec 64) :=
.call (some (([12, 32, 22, 44, 8, 30]), ((Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody723_0, 723, 4)) (some 721) ([20]) (some (20, sourceBody723_29, 723, 5))

def sourceBody723_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_30 sourceBody723_5

def sourceBody723_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_31 sourceBody723_0

def sourceBody723_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_28 sourceBody723_32

def sourceBody723_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 12)

def sourceBody723_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 32)

def sourceBody723_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 22)

def sourceBody723_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 44)

def sourceBody723_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 8)

def sourceBody723_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 30)

def sourceBody723_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 13402431016077863595#64)

def sourceBody723_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 2210141511517208575#64)

def sourceBody723_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.const 7435674573564081700#64)

def sourceBody723_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 7239337960414712511#64)

def sourceBody723_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 5412103778470702295#64)

def sourceBody723_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 1873798617647539866#64)

def sourceBody723_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 42

def sourceBody723_47 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)
        PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody723_0, 723, 6)) (some 703) ([42, 16, 36, 26, 48, 6, 28, 18, 40, 14, 34, 24]) (some (42, sourceBody723_46, 723, 7))

def sourceBody723_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_47 sourceBody723_5

def sourceBody723_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_48 sourceBody723_0

def sourceBody723_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_45 sourceBody723_49

def sourceBody723_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_44 sourceBody723_50

def sourceBody723_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_43 sourceBody723_51

def sourceBody723_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_42 sourceBody723_52

def sourceBody723_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_41 sourceBody723_53

def sourceBody723_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_40 sourceBody723_54

def sourceBody723_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_39 sourceBody723_55

def sourceBody723_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_38 sourceBody723_56

def sourceBody723_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_37 sourceBody723_57

def sourceBody723_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_36 sourceBody723_58

def sourceBody723_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_35 sourceBody723_59

def sourceBody723_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_34 sourceBody723_60

def sourceBody723_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 20)

def sourceBody723_63 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody723_64 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody723_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody723_66 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 16 (Flapjack.WordRegImm.reg 36) sourceBody723_64 sourceBody723_65

def sourceBody723_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_66 sourceBody723_5

def sourceBody723_68 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 16)

def sourceBody723_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody723_70 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [42]

def sourceBody723_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_70 sourceBody723_0

def sourceBody723_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_69 sourceBody723_71

def sourceBody723_73 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 26 (Flapjack.WordRegImm.imm 0#64) sourceBody723_72 sourceBody723_0

def sourceBody723_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_73 sourceBody723_5

def sourceBody723_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_74 sourceBody723_0

def sourceBody723_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_68 sourceBody723_75

def sourceBody723_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_67 sourceBody723_76

def sourceBody723_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_63 sourceBody723_77

def sourceBody723_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_62 sourceBody723_78

def sourceBody723_80 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 12)

def sourceBody723_81 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 32)

def sourceBody723_82 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 22)

def sourceBody723_83 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 44)

def sourceBody723_84 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 8)

def sourceBody723_85 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 30)

def sourceBody723_86 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 28

def sourceBody723_87 : WordLangProgHOL (BitVec 64) :=
.call (some (([42, 16, 36, 26, 48, 6]), ((Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody723_0, 723, 8)) (some 712) ([28, 18, 40, 14, 34, 24]) (some (28, sourceBody723_86, 723, 9))

def sourceBody723_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_87 sourceBody723_5

def sourceBody723_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_88 sourceBody723_0

def sourceBody723_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_85 sourceBody723_89

def sourceBody723_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_84 sourceBody723_90

def sourceBody723_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_83 sourceBody723_91

def sourceBody723_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_82 sourceBody723_92

def sourceBody723_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_81 sourceBody723_93

def sourceBody723_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_80 sourceBody723_94

def sourceBody723_96 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 4)

def sourceBody723_97 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 42)

def sourceBody723_98 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 16)

def sourceBody723_99 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 36)

def sourceBody723_100 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 26)

def sourceBody723_101 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 48)

def sourceBody723_102 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 6)

def sourceBody723_103 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 18)

def sourceBody723_104 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 28) 10

def sourceBody723_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_104 sourceBody723_0

def sourceBody723_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_103 sourceBody723_105

def sourceBody723_107 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 40)

def sourceBody723_108 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 28, Flapjack.WordLangExpHOL.const 8#64])
  10

def sourceBody723_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_108 sourceBody723_0

def sourceBody723_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_107 sourceBody723_109

def sourceBody723_111 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 14)

def sourceBody723_112 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 28, Flapjack.WordLangExpHOL.const 16#64])
  10

def sourceBody723_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_112 sourceBody723_0

def sourceBody723_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_111 sourceBody723_113

def sourceBody723_115 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 34)

def sourceBody723_116 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 28, Flapjack.WordLangExpHOL.const 24#64])
  10

def sourceBody723_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_116 sourceBody723_0

def sourceBody723_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_115 sourceBody723_117

def sourceBody723_119 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 24)

def sourceBody723_120 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 28, Flapjack.WordLangExpHOL.const 32#64])
  10

def sourceBody723_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_120 sourceBody723_0

def sourceBody723_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_119 sourceBody723_121

def sourceBody723_123 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 46)

def sourceBody723_124 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 28, Flapjack.WordLangExpHOL.const 40#64])
  10

def sourceBody723_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_124 sourceBody723_0

def sourceBody723_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_123 sourceBody723_125

def sourceBody723_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_126 sourceBody723_0

def sourceBody723_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_122 sourceBody723_127

def sourceBody723_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_118 sourceBody723_128

def sourceBody723_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_114 sourceBody723_129

def sourceBody723_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_110 sourceBody723_130

def sourceBody723_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_106 sourceBody723_131

def sourceBody723_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_102 sourceBody723_132

def sourceBody723_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_0 sourceBody723_133

def sourceBody723_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_101 sourceBody723_134

def sourceBody723_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_0 sourceBody723_135

def sourceBody723_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_100 sourceBody723_136

def sourceBody723_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_0 sourceBody723_137

def sourceBody723_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_99 sourceBody723_138

def sourceBody723_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_0 sourceBody723_139

def sourceBody723_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_98 sourceBody723_140

def sourceBody723_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_0 sourceBody723_141

def sourceBody723_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_97 sourceBody723_142

def sourceBody723_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_0 sourceBody723_143

def sourceBody723_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_96 sourceBody723_144

def sourceBody723_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_0 sourceBody723_145

def sourceBody723_147 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody723_148 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [28]

def sourceBody723_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_148 sourceBody723_0

def sourceBody723_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_147 sourceBody723_149

def sourceBody723_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_146 sourceBody723_150

def sourceBody723_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_95 sourceBody723_151

def sourceBody723_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_0 sourceBody723_152

def sourceBody723_154 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_0 sourceBody723_153

def sourceBody723_155 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_0 sourceBody723_154

def sourceBody723_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_0 sourceBody723_155

def sourceBody723_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_0 sourceBody723_156

def sourceBody723_158 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_0 sourceBody723_157

def sourceBody723_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_0 sourceBody723_158

def sourceBody723_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_0 sourceBody723_159

def sourceBody723_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_0 sourceBody723_160

def sourceBody723_162 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_0 sourceBody723_161

def sourceBody723_163 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_0 sourceBody723_162

def sourceBody723_164 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_0 sourceBody723_163

def sourceBody723_165 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_79 sourceBody723_164

def sourceBody723_166 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_61 sourceBody723_165

def sourceBody723_167 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_0 sourceBody723_166

def sourceBody723_168 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_0 sourceBody723_167

def sourceBody723_169 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_33 sourceBody723_168

def sourceBody723_170 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_0 sourceBody723_169

def sourceBody723_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_0 sourceBody723_170

def sourceBody723_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_0 sourceBody723_171

def sourceBody723_173 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_0 sourceBody723_172

def sourceBody723_174 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_0 sourceBody723_173

def sourceBody723_175 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_0 sourceBody723_174

def sourceBody723_176 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_0 sourceBody723_175

def sourceBody723_177 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_0 sourceBody723_176

def sourceBody723_178 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_0 sourceBody723_177

def sourceBody723_179 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_0 sourceBody723_178

def sourceBody723_180 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_0 sourceBody723_179

def sourceBody723_181 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_0 sourceBody723_180

def sourceBody723_182 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_27 sourceBody723_181

def sourceBody723_183 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_9 sourceBody723_182

def sourceBody723_184 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_0 sourceBody723_183

def sourceBody723_185 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody723_0 sourceBody723_184

def source723 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (723, 3, sourceBody723_185)
end InitECandidate.Proofs.WordStages
