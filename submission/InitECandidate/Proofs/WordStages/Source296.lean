import InitECandidate.Proofs.WordStages.Source280
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody296_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody296_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody296_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody296_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody296_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 4)

def sourceBody296_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 6)

def sourceBody296_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody296_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody296_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_0 sourceBody296_0

def sourceBody296_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_8 sourceBody296_0

def sourceBody296_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 3#64)

def sourceBody296_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody296_12 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit))
      PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody296_0, 296, 3)) (some 282) ([14]) (some (14, sourceBody296_11, 296, 4))

def sourceBody296_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_12 sourceBody296_7

def sourceBody296_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_13 sourceBody296_0

def sourceBody296_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_10 sourceBody296_14

def sourceBody296_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_0 sourceBody296_15

def sourceBody296_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_0 sourceBody296_16

def sourceBody296_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_9 sourceBody296_17

def sourceBody296_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_7 sourceBody296_18

def sourceBody296_20 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 20 (Flapjack.WordRegImm.imm 1#64) sourceBody296_6 sourceBody296_19

def sourceBody296_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_20 sourceBody296_7

def sourceBody296_22 : WordLangProgHOL (BitVec 64) :=
.call (some (([10, 22, 16, 28]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit))
      PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody296_0, 296, 2)) (some 161) ([20, 14]) (some (20, sourceBody296_21, 296, 5))

def sourceBody296_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_22 sourceBody296_7

def sourceBody296_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_23 sourceBody296_0

def sourceBody296_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_5 sourceBody296_24

def sourceBody296_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_4 sourceBody296_25

def sourceBody296_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 10)

def sourceBody296_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody296_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody296_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody296_31 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 14 (Flapjack.WordRegImm.reg 26) sourceBody296_29 sourceBody296_30

def sourceBody296_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_31 sourceBody296_7

def sourceBody296_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 14)

def sourceBody296_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 16)

def sourceBody296_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody296_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody296_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [20, 14, 26, 12]

def sourceBody296_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_37 sourceBody296_0

def sourceBody296_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_36 sourceBody296_38

def sourceBody296_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_28 sourceBody296_39

def sourceBody296_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_30 sourceBody296_40

def sourceBody296_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_35 sourceBody296_41

def sourceBody296_43 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.imm 0#64) sourceBody296_42 sourceBody296_0

def sourceBody296_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_43 sourceBody296_7

def sourceBody296_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_44 sourceBody296_0

def sourceBody296_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_33 sourceBody296_45

def sourceBody296_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_32 sourceBody296_46

def sourceBody296_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_28 sourceBody296_47

def sourceBody296_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_34 sourceBody296_48

def sourceBody296_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody296_51 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.WordRegImm.reg 26) sourceBody296_29 sourceBody296_30

def sourceBody296_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_51 sourceBody296_7

def sourceBody296_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 10#64)

def sourceBody296_54 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
      PUnit.unit Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody296_0, 296, 6)) (some 282) ([14]) (some (14, sourceBody296_11, 296, 7))

def sourceBody296_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_54 sourceBody296_7

def sourceBody296_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_55 sourceBody296_0

def sourceBody296_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_53 sourceBody296_56

def sourceBody296_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_0 sourceBody296_57

def sourceBody296_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_0 sourceBody296_58

def sourceBody296_60 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.imm 0#64) sourceBody296_59 sourceBody296_0

def sourceBody296_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_60 sourceBody296_7

def sourceBody296_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_61 sourceBody296_0

def sourceBody296_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_33 sourceBody296_62

def sourceBody296_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_52 sourceBody296_63

def sourceBody296_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_50 sourceBody296_64

def sourceBody296_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_34 sourceBody296_65

def sourceBody296_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_49 sourceBody296_66

def sourceBody296_68 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 2)

def sourceBody296_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 22)

def sourceBody296_70 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody296_71 : WordLangProgHOL (BitVec 64) :=
.call (some (([20, 14, 26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody296_0, 296, 8)) (some 290) ([12, 24]) (some (12, sourceBody296_70, 296, 9))

def sourceBody296_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_71 sourceBody296_7

def sourceBody296_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_72 sourceBody296_0

def sourceBody296_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_69 sourceBody296_73

def sourceBody296_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_68 sourceBody296_74

def sourceBody296_76 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 20)

def sourceBody296_77 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody296_78 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody296_79 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody296_80 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 24 (Flapjack.WordRegImm.reg 18) sourceBody296_78 sourceBody296_79

def sourceBody296_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_80 sourceBody296_7

def sourceBody296_82 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 24)

def sourceBody296_83 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 24

def sourceBody296_84 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody296_0, 296, 10)) (some 291) ([24]) (some (24, sourceBody296_83, 296, 11))

def sourceBody296_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_84 sourceBody296_7

def sourceBody296_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_85 sourceBody296_0

def sourceBody296_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_69 sourceBody296_86

def sourceBody296_88 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 12)

def sourceBody296_89 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody296_90 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody296_91 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [24, 18, 30, 8]

def sourceBody296_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_91 sourceBody296_0

def sourceBody296_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_90 sourceBody296_92

def sourceBody296_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_89 sourceBody296_93

def sourceBody296_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_88 sourceBody296_94

def sourceBody296_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_79 sourceBody296_95

def sourceBody296_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_87 sourceBody296_96

def sourceBody296_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_0 sourceBody296_97

def sourceBody296_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_0 sourceBody296_98

def sourceBody296_100 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 30 (Flapjack.WordRegImm.imm 0#64) sourceBody296_99 sourceBody296_0

def sourceBody296_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_100 sourceBody296_7

def sourceBody296_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_101 sourceBody296_0

def sourceBody296_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_82 sourceBody296_102

def sourceBody296_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_81 sourceBody296_103

def sourceBody296_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_77 sourceBody296_104

def sourceBody296_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_76 sourceBody296_105

def sourceBody296_107 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody296_108 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 14)

def sourceBody296_109 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 26)

def sourceBody296_110 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 22)

def sourceBody296_111 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [12, 24, 18, 30]

def sourceBody296_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_111 sourceBody296_0

def sourceBody296_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_110 sourceBody296_112

def sourceBody296_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_109 sourceBody296_113

def sourceBody296_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_108 sourceBody296_114

def sourceBody296_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_107 sourceBody296_115

def sourceBody296_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_106 sourceBody296_116

def sourceBody296_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_75 sourceBody296_117

def sourceBody296_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_0 sourceBody296_118

def sourceBody296_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_0 sourceBody296_119

def sourceBody296_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_0 sourceBody296_120

def sourceBody296_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_0 sourceBody296_121

def sourceBody296_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_0 sourceBody296_122

def sourceBody296_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_0 sourceBody296_123

def sourceBody296_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_67 sourceBody296_124

def sourceBody296_126 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.imm 0#64) sourceBody296_125 sourceBody296_0

def sourceBody296_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_126 sourceBody296_7

def sourceBody296_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_127 sourceBody296_0

def sourceBody296_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_33 sourceBody296_128

def sourceBody296_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_32 sourceBody296_129

def sourceBody296_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_28 sourceBody296_130

def sourceBody296_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_27 sourceBody296_131

def sourceBody296_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_26 sourceBody296_132

def sourceBody296_134 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody296_135 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 4)

def sourceBody296_136 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 6)

def sourceBody296_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_136 sourceBody296_39

def sourceBody296_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_135 sourceBody296_137

def sourceBody296_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_134 sourceBody296_138

def sourceBody296_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_133 sourceBody296_139

def sourceBody296_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_0 sourceBody296_140

def sourceBody296_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_0 sourceBody296_141

def sourceBody296_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_0 sourceBody296_142

def sourceBody296_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_0 sourceBody296_143

def sourceBody296_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_3 sourceBody296_144

def sourceBody296_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_0 sourceBody296_145

def sourceBody296_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_2 sourceBody296_146

def sourceBody296_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_0 sourceBody296_147

def sourceBody296_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_1 sourceBody296_148

def sourceBody296_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody296_0 sourceBody296_149

def source296 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (296, 4, sourceBody296_150)
end InitECandidate.Proofs.WordStages
