import InitECandidate.Proofs.WordStages.Source817
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody833_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 2)

def sourceBody833_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody833_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody833_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody833_4 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 10 (Flapjack.WordRegImm.reg 4) sourceBody833_2 sourceBody833_3

def sourceBody833_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody833_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_4 sourceBody833_5

def sourceBody833_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 10)

def sourceBody833_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody833_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody833_10 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody833_8, 833, 2)) (some 828) ([]) (some (10, sourceBody833_9, 833, 3))

def sourceBody833_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_10 sourceBody833_5

def sourceBody833_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_11 sourceBody833_8

def sourceBody833_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_8 sourceBody833_12

def sourceBody833_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_8 sourceBody833_13

def sourceBody833_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody833_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [6]

def sourceBody833_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_16 sourceBody833_8

def sourceBody833_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_15 sourceBody833_17

def sourceBody833_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_14 sourceBody833_18

def sourceBody833_20 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.WordRegImm.imm 0#64) sourceBody833_19 sourceBody833_8

def sourceBody833_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_20 sourceBody833_5

def sourceBody833_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_21 sourceBody833_8

def sourceBody833_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_7 sourceBody833_22

def sourceBody833_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_6 sourceBody833_23

def sourceBody833_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_1 sourceBody833_24

def sourceBody833_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_0 sourceBody833_25

def sourceBody833_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 2#64)

def sourceBody833_28 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody833_8, 833, 4)) (some 827) ([]) (some (10, sourceBody833_9, 833, 5))

def sourceBody833_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_28 sourceBody833_5

def sourceBody833_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_29 sourceBody833_8

def sourceBody833_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_8 sourceBody833_30

def sourceBody833_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_8 sourceBody833_31

def sourceBody833_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_32 sourceBody833_18

def sourceBody833_34 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.WordRegImm.imm 0#64) sourceBody833_33 sourceBody833_8

def sourceBody833_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_34 sourceBody833_5

def sourceBody833_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_35 sourceBody833_8

def sourceBody833_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_7 sourceBody833_36

def sourceBody833_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_6 sourceBody833_37

def sourceBody833_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_27 sourceBody833_38

def sourceBody833_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_0 sourceBody833_39

def sourceBody833_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_26 sourceBody833_40

def sourceBody833_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 3#64)

def sourceBody833_43 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody833_8, 833, 6)) (some 829) ([]) (some (10, sourceBody833_9, 833, 7))

def sourceBody833_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_43 sourceBody833_5

def sourceBody833_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_44 sourceBody833_8

def sourceBody833_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_8 sourceBody833_45

def sourceBody833_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_8 sourceBody833_46

def sourceBody833_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_47 sourceBody833_18

def sourceBody833_49 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.WordRegImm.imm 0#64) sourceBody833_48 sourceBody833_8

def sourceBody833_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_49 sourceBody833_5

def sourceBody833_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_50 sourceBody833_8

def sourceBody833_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_7 sourceBody833_51

def sourceBody833_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_6 sourceBody833_52

def sourceBody833_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_42 sourceBody833_53

def sourceBody833_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_0 sourceBody833_54

def sourceBody833_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_41 sourceBody833_55

def sourceBody833_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 4#64)

def sourceBody833_58 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody833_8, 833, 8)) (some 826) ([]) (some (10, sourceBody833_9, 833, 9))

def sourceBody833_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_58 sourceBody833_5

def sourceBody833_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_59 sourceBody833_8

def sourceBody833_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_8 sourceBody833_60

def sourceBody833_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_8 sourceBody833_61

def sourceBody833_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_62 sourceBody833_18

def sourceBody833_64 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.WordRegImm.imm 0#64) sourceBody833_63 sourceBody833_8

def sourceBody833_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_64 sourceBody833_5

def sourceBody833_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_65 sourceBody833_8

def sourceBody833_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_7 sourceBody833_66

def sourceBody833_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_6 sourceBody833_67

def sourceBody833_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_57 sourceBody833_68

def sourceBody833_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_0 sourceBody833_69

def sourceBody833_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_56 sourceBody833_70

def sourceBody833_72 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 6#64)

def sourceBody833_73 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody833_8, 833, 10)) (some 697) ([]) (some (10, sourceBody833_9, 833, 11))

def sourceBody833_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_73 sourceBody833_5

def sourceBody833_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_74 sourceBody833_8

def sourceBody833_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_8 sourceBody833_75

def sourceBody833_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_8 sourceBody833_76

def sourceBody833_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_77 sourceBody833_18

def sourceBody833_79 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.WordRegImm.imm 0#64) sourceBody833_78 sourceBody833_8

def sourceBody833_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_79 sourceBody833_5

def sourceBody833_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_80 sourceBody833_8

def sourceBody833_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_7 sourceBody833_81

def sourceBody833_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_6 sourceBody833_82

def sourceBody833_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_72 sourceBody833_83

def sourceBody833_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_0 sourceBody833_84

def sourceBody833_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_71 sourceBody833_85

def sourceBody833_87 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 7#64)

def sourceBody833_88 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody833_8, 833, 12)) (some 698) ([]) (some (10, sourceBody833_9, 833, 13))

def sourceBody833_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_88 sourceBody833_5

def sourceBody833_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_89 sourceBody833_8

def sourceBody833_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_8 sourceBody833_90

def sourceBody833_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_8 sourceBody833_91

def sourceBody833_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_92 sourceBody833_18

def sourceBody833_94 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.WordRegImm.imm 0#64) sourceBody833_93 sourceBody833_8

def sourceBody833_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_94 sourceBody833_5

def sourceBody833_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_95 sourceBody833_8

def sourceBody833_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_7 sourceBody833_96

def sourceBody833_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_6 sourceBody833_97

def sourceBody833_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_87 sourceBody833_98

def sourceBody833_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_0 sourceBody833_99

def sourceBody833_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_86 sourceBody833_100

def sourceBody833_102 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 8#64)

def sourceBody833_103 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody833_8, 833, 14)) (some 699) ([]) (some (10, sourceBody833_9, 833, 15))

def sourceBody833_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_103 sourceBody833_5

def sourceBody833_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_104 sourceBody833_8

def sourceBody833_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_8 sourceBody833_105

def sourceBody833_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_8 sourceBody833_106

def sourceBody833_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_107 sourceBody833_18

def sourceBody833_109 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.WordRegImm.imm 0#64) sourceBody833_108 sourceBody833_8

def sourceBody833_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_109 sourceBody833_5

def sourceBody833_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_110 sourceBody833_8

def sourceBody833_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_7 sourceBody833_111

def sourceBody833_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_6 sourceBody833_112

def sourceBody833_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_102 sourceBody833_113

def sourceBody833_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_0 sourceBody833_114

def sourceBody833_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_101 sourceBody833_115

def sourceBody833_117 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 5#64)

def sourceBody833_118 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody833_8, 833, 16)) (some 832) ([]) (some (10, sourceBody833_9, 833, 17))

def sourceBody833_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_118 sourceBody833_5

def sourceBody833_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_119 sourceBody833_8

def sourceBody833_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_8 sourceBody833_120

def sourceBody833_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_8 sourceBody833_121

def sourceBody833_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_122 sourceBody833_18

def sourceBody833_124 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.WordRegImm.imm 0#64) sourceBody833_123 sourceBody833_8

def sourceBody833_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_124 sourceBody833_5

def sourceBody833_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_125 sourceBody833_8

def sourceBody833_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_7 sourceBody833_126

def sourceBody833_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_6 sourceBody833_127

def sourceBody833_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_117 sourceBody833_128

def sourceBody833_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_0 sourceBody833_129

def sourceBody833_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_116 sourceBody833_130

def sourceBody833_132 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 9#64)

def sourceBody833_133 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody833_8, 833, 18)) (some 830) ([]) (some (10, sourceBody833_9, 833, 19))

def sourceBody833_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_133 sourceBody833_5

def sourceBody833_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_134 sourceBody833_8

def sourceBody833_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_8 sourceBody833_135

def sourceBody833_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_8 sourceBody833_136

def sourceBody833_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_137 sourceBody833_18

def sourceBody833_139 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.WordRegImm.imm 0#64) sourceBody833_138 sourceBody833_8

def sourceBody833_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_139 sourceBody833_5

def sourceBody833_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_140 sourceBody833_8

def sourceBody833_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_7 sourceBody833_141

def sourceBody833_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_6 sourceBody833_142

def sourceBody833_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_132 sourceBody833_143

def sourceBody833_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_0 sourceBody833_144

def sourceBody833_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_131 sourceBody833_145

def sourceBody833_147 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 10#64)

def sourceBody833_148 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody833_8, 833, 20)) (some 824) ([]) (some (10, sourceBody833_9, 833, 21))

def sourceBody833_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_148 sourceBody833_5

def sourceBody833_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_149 sourceBody833_8

def sourceBody833_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_8 sourceBody833_150

def sourceBody833_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_8 sourceBody833_151

def sourceBody833_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_152 sourceBody833_18

def sourceBody833_154 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.WordRegImm.imm 0#64) sourceBody833_153 sourceBody833_8

def sourceBody833_155 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_154 sourceBody833_5

def sourceBody833_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_155 sourceBody833_8

def sourceBody833_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_7 sourceBody833_156

def sourceBody833_158 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_6 sourceBody833_157

def sourceBody833_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_147 sourceBody833_158

def sourceBody833_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_0 sourceBody833_159

def sourceBody833_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_146 sourceBody833_160

def sourceBody833_162 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 11#64)

def sourceBody833_163 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody833_8, 833, 22)) (some 817) ([]) (some (10, sourceBody833_9, 833, 23))

def sourceBody833_164 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_163 sourceBody833_5

def sourceBody833_165 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_164 sourceBody833_8

def sourceBody833_166 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_8 sourceBody833_165

def sourceBody833_167 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_8 sourceBody833_166

def sourceBody833_168 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_167 sourceBody833_18

def sourceBody833_169 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.WordRegImm.imm 0#64) sourceBody833_168 sourceBody833_8

def sourceBody833_170 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_169 sourceBody833_5

def sourceBody833_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_170 sourceBody833_8

def sourceBody833_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_7 sourceBody833_171

def sourceBody833_173 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_6 sourceBody833_172

def sourceBody833_174 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_162 sourceBody833_173

def sourceBody833_175 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_0 sourceBody833_174

def sourceBody833_176 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_161 sourceBody833_175

def sourceBody833_177 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 12#64)

def sourceBody833_178 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody833_8, 833, 24)) (some 818) ([]) (some (10, sourceBody833_9, 833, 25))

def sourceBody833_179 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_178 sourceBody833_5

def sourceBody833_180 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_179 sourceBody833_8

def sourceBody833_181 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_8 sourceBody833_180

def sourceBody833_182 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_8 sourceBody833_181

def sourceBody833_183 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_182 sourceBody833_18

def sourceBody833_184 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.WordRegImm.imm 0#64) sourceBody833_183 sourceBody833_8

def sourceBody833_185 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_184 sourceBody833_5

def sourceBody833_186 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_185 sourceBody833_8

def sourceBody833_187 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_7 sourceBody833_186

def sourceBody833_188 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_6 sourceBody833_187

def sourceBody833_189 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_177 sourceBody833_188

def sourceBody833_190 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_0 sourceBody833_189

def sourceBody833_191 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_176 sourceBody833_190

def sourceBody833_192 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 13#64)

def sourceBody833_193 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody833_8, 833, 26)) (some 819) ([]) (some (10, sourceBody833_9, 833, 27))

def sourceBody833_194 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_193 sourceBody833_5

def sourceBody833_195 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_194 sourceBody833_8

def sourceBody833_196 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_8 sourceBody833_195

def sourceBody833_197 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_8 sourceBody833_196

def sourceBody833_198 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_197 sourceBody833_18

def sourceBody833_199 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.WordRegImm.imm 0#64) sourceBody833_198 sourceBody833_8

def sourceBody833_200 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_199 sourceBody833_5

def sourceBody833_201 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_200 sourceBody833_8

def sourceBody833_202 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_7 sourceBody833_201

def sourceBody833_203 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_6 sourceBody833_202

def sourceBody833_204 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_192 sourceBody833_203

def sourceBody833_205 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_0 sourceBody833_204

def sourceBody833_206 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_191 sourceBody833_205

def sourceBody833_207 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 14#64)

def sourceBody833_208 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody833_8, 833, 28)) (some 820) ([]) (some (10, sourceBody833_9, 833, 29))

def sourceBody833_209 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_208 sourceBody833_5

def sourceBody833_210 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_209 sourceBody833_8

def sourceBody833_211 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_8 sourceBody833_210

def sourceBody833_212 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_8 sourceBody833_211

def sourceBody833_213 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_212 sourceBody833_18

def sourceBody833_214 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.WordRegImm.imm 0#64) sourceBody833_213 sourceBody833_8

def sourceBody833_215 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_214 sourceBody833_5

def sourceBody833_216 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_215 sourceBody833_8

def sourceBody833_217 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_7 sourceBody833_216

def sourceBody833_218 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_6 sourceBody833_217

def sourceBody833_219 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_207 sourceBody833_218

def sourceBody833_220 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_0 sourceBody833_219

def sourceBody833_221 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_206 sourceBody833_220

def sourceBody833_222 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 15#64)

def sourceBody833_223 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody833_8, 833, 30)) (some 821) ([]) (some (10, sourceBody833_9, 833, 31))

def sourceBody833_224 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_223 sourceBody833_5

def sourceBody833_225 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_224 sourceBody833_8

def sourceBody833_226 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_8 sourceBody833_225

def sourceBody833_227 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_8 sourceBody833_226

def sourceBody833_228 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_227 sourceBody833_18

def sourceBody833_229 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.WordRegImm.imm 0#64) sourceBody833_228 sourceBody833_8

def sourceBody833_230 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_229 sourceBody833_5

def sourceBody833_231 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_230 sourceBody833_8

def sourceBody833_232 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_7 sourceBody833_231

def sourceBody833_233 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_6 sourceBody833_232

def sourceBody833_234 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_222 sourceBody833_233

def sourceBody833_235 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_0 sourceBody833_234

def sourceBody833_236 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_221 sourceBody833_235

def sourceBody833_237 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 16#64)

def sourceBody833_238 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody833_8, 833, 32)) (some 822) ([]) (some (10, sourceBody833_9, 833, 33))

def sourceBody833_239 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_238 sourceBody833_5

def sourceBody833_240 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_239 sourceBody833_8

def sourceBody833_241 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_8 sourceBody833_240

def sourceBody833_242 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_8 sourceBody833_241

def sourceBody833_243 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_242 sourceBody833_18

def sourceBody833_244 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.WordRegImm.imm 0#64) sourceBody833_243 sourceBody833_8

def sourceBody833_245 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_244 sourceBody833_5

def sourceBody833_246 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_245 sourceBody833_8

def sourceBody833_247 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_7 sourceBody833_246

def sourceBody833_248 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_6 sourceBody833_247

def sourceBody833_249 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_237 sourceBody833_248

def sourceBody833_250 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_0 sourceBody833_249

def sourceBody833_251 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_236 sourceBody833_250

def sourceBody833_252 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 17#64)

def sourceBody833_253 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody833_8, 833, 34)) (some 823) ([]) (some (10, sourceBody833_9, 833, 35))

def sourceBody833_254 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_253 sourceBody833_5

def sourceBody833_255 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_254 sourceBody833_8

def sourceBody833_256 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_8 sourceBody833_255

def sourceBody833_257 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_8 sourceBody833_256

def sourceBody833_258 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_257 sourceBody833_18

def sourceBody833_259 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.WordRegImm.imm 0#64) sourceBody833_258 sourceBody833_8

def sourceBody833_260 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_259 sourceBody833_5

def sourceBody833_261 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_260 sourceBody833_8

def sourceBody833_262 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_7 sourceBody833_261

def sourceBody833_263 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_6 sourceBody833_262

def sourceBody833_264 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_252 sourceBody833_263

def sourceBody833_265 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_0 sourceBody833_264

def sourceBody833_266 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_251 sourceBody833_265

def sourceBody833_267 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 18#64)

def sourceBody833_268 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody833_8, 833, 36)) (some 652) ([]) (some (10, sourceBody833_9, 833, 37))

def sourceBody833_269 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_268 sourceBody833_5

def sourceBody833_270 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_269 sourceBody833_8

def sourceBody833_271 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_8 sourceBody833_270

def sourceBody833_272 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_8 sourceBody833_271

def sourceBody833_273 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_272 sourceBody833_18

def sourceBody833_274 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.WordRegImm.imm 0#64) sourceBody833_273 sourceBody833_8

def sourceBody833_275 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_274 sourceBody833_5

def sourceBody833_276 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_275 sourceBody833_8

def sourceBody833_277 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_7 sourceBody833_276

def sourceBody833_278 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_6 sourceBody833_277

def sourceBody833_279 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_267 sourceBody833_278

def sourceBody833_280 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_0 sourceBody833_279

def sourceBody833_281 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_266 sourceBody833_280

def sourceBody833_282 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 99#64)

def sourceBody833_283 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 6)

def sourceBody833_284 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_283 sourceBody833_8

def sourceBody833_285 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_284 sourceBody833_8

def sourceBody833_286 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_282 sourceBody833_285

def sourceBody833_287 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_8 sourceBody833_286

def sourceBody833_288 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 4#64)

def sourceBody833_289 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody833_290 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_288 sourceBody833_289

def sourceBody833_291 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_287 sourceBody833_290

def sourceBody833_292 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_281 sourceBody833_291

def sourceBody833_293 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody833_292 sourceBody833_18

def source833 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (833, 2, sourceBody833_293)
end InitECandidate.Proofs.WordStages
