import InitECandidate.Proofs.WordStages.Source691
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody707_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody707_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 2)

def sourceBody707_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 68 (Flapjack.WordLangExpHOL.var 4)

def sourceBody707_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.var 6)

def sourceBody707_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 84 (Flapjack.WordLangExpHOL.var 8)

def sourceBody707_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 10)

def sourceBody707_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 64 (Flapjack.WordLangExpHOL.var 12)

def sourceBody707_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 14)

def sourceBody707_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 80 (Flapjack.WordLangExpHOL.var 16)

def sourceBody707_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 18)

def sourceBody707_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 72 (Flapjack.WordLangExpHOL.var 20)

def sourceBody707_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.var 22)

def sourceBody707_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 88 (Flapjack.WordLangExpHOL.var 24)

def sourceBody707_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 36

def sourceBody707_14 : WordLangProgHOL (BitVec 64) :=
.call (some (([70, 54, 86, 28, 60, 44, 76]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody707_0, 707, 2)) (some 705) ([36, 68, 52, 84, 32, 64, 48, 80, 40, 72, 56, 88]) (some (36, sourceBody707_13, 707, 3))

def sourceBody707_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody707_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_14 sourceBody707_15

def sourceBody707_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_16 sourceBody707_0

def sourceBody707_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_12 sourceBody707_17

def sourceBody707_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_11 sourceBody707_18

def sourceBody707_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_10 sourceBody707_19

def sourceBody707_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_9 sourceBody707_20

def sourceBody707_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_8 sourceBody707_21

def sourceBody707_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_7 sourceBody707_22

def sourceBody707_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_6 sourceBody707_23

def sourceBody707_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_5 sourceBody707_24

def sourceBody707_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_4 sourceBody707_25

def sourceBody707_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_3 sourceBody707_26

def sourceBody707_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_2 sourceBody707_27

def sourceBody707_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_1 sourceBody707_28

def sourceBody707_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 70)

def sourceBody707_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 68 (Flapjack.WordLangExpHOL.var 54)

def sourceBody707_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.var 86)

def sourceBody707_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 84 (Flapjack.WordLangExpHOL.var 28)

def sourceBody707_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 60)

def sourceBody707_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 64 (Flapjack.WordLangExpHOL.var 44)

def sourceBody707_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 80 (Flapjack.WordLangExpHOL.var 76)

def sourceBody707_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody707_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 80 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody707_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 80 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody707_40 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 80 (Flapjack.WordRegImm.reg 40) sourceBody707_38 sourceBody707_39

def sourceBody707_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_40 sourceBody707_15

def sourceBody707_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 72 (Flapjack.WordLangExpHOL.var 80)

def sourceBody707_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 36)

def sourceBody707_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 80 (Flapjack.WordLangExpHOL.var 68)

def sourceBody707_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 52)

def sourceBody707_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 72 (Flapjack.WordLangExpHOL.var 84)

def sourceBody707_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.var 32)

def sourceBody707_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 88 (Flapjack.WordLangExpHOL.var 64)

def sourceBody707_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [48, 80, 40, 72, 56, 88]

def sourceBody707_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_49 sourceBody707_0

def sourceBody707_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_48 sourceBody707_50

def sourceBody707_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_47 sourceBody707_51

def sourceBody707_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_46 sourceBody707_52

def sourceBody707_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_45 sourceBody707_53

def sourceBody707_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_44 sourceBody707_54

def sourceBody707_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_43 sourceBody707_55

def sourceBody707_57 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 72 (Flapjack.WordRegImm.imm 0#64) sourceBody707_56 sourceBody707_0

def sourceBody707_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_57 sourceBody707_15

def sourceBody707_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_58 sourceBody707_0

def sourceBody707_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_42 sourceBody707_59

def sourceBody707_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_41 sourceBody707_60

def sourceBody707_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_37 sourceBody707_61

def sourceBody707_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_36 sourceBody707_62

def sourceBody707_64 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.var 36)

def sourceBody707_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 68)

def sourceBody707_66 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 74 (Flapjack.WordLangExpHOL.var 52)

def sourceBody707_67 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 84)

def sourceBody707_68 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 66 (Flapjack.WordLangExpHOL.var 32)

def sourceBody707_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 64)

def sourceBody707_70 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 82 (Flapjack.WordLangExpHOL.const 13402431016077863595#64)

def sourceBody707_71 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 2210141511517208575#64)

def sourceBody707_72 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 62 (Flapjack.WordLangExpHOL.const 7435674573564081700#64)

def sourceBody707_73 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.const 7239337960414712511#64)

def sourceBody707_74 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 78 (Flapjack.WordLangExpHOL.const 5412103778470702295#64)

def sourceBody707_75 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.const 1873798617647539866#64)

def sourceBody707_76 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 58

def sourceBody707_77 : WordLangProgHOL (BitVec 64) :=
.call (some (([48, 80, 40, 72, 56, 88, 26]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody707_0, 707, 4)) (some 704) ([58, 42, 74, 34, 66, 50, 82, 30, 62, 46, 78, 38]) (some (58, sourceBody707_76, 707, 5))

def sourceBody707_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_77 sourceBody707_15

def sourceBody707_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_78 sourceBody707_0

def sourceBody707_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_75 sourceBody707_79

def sourceBody707_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_74 sourceBody707_80

def sourceBody707_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_73 sourceBody707_81

def sourceBody707_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_72 sourceBody707_82

def sourceBody707_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_71 sourceBody707_83

def sourceBody707_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_70 sourceBody707_84

def sourceBody707_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_69 sourceBody707_85

def sourceBody707_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_68 sourceBody707_86

def sourceBody707_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_67 sourceBody707_87

def sourceBody707_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_66 sourceBody707_88

def sourceBody707_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_65 sourceBody707_89

def sourceBody707_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_64 sourceBody707_90

def sourceBody707_92 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.var 48)

def sourceBody707_93 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 80)

def sourceBody707_94 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 74 (Flapjack.WordLangExpHOL.var 40)

def sourceBody707_95 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 72)

def sourceBody707_96 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 66 (Flapjack.WordLangExpHOL.var 56)

def sourceBody707_97 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 88)

def sourceBody707_98 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [58, 42, 74, 34, 66, 50]

def sourceBody707_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_98 sourceBody707_0

def sourceBody707_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_97 sourceBody707_99

def sourceBody707_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_96 sourceBody707_100

def sourceBody707_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_95 sourceBody707_101

def sourceBody707_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_94 sourceBody707_102

def sourceBody707_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_93 sourceBody707_103

def sourceBody707_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_92 sourceBody707_104

def sourceBody707_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_91 sourceBody707_105

def sourceBody707_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_0 sourceBody707_106

def sourceBody707_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_0 sourceBody707_107

def sourceBody707_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_0 sourceBody707_108

def sourceBody707_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_0 sourceBody707_109

def sourceBody707_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_0 sourceBody707_110

def sourceBody707_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_0 sourceBody707_111

def sourceBody707_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_0 sourceBody707_112

def sourceBody707_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_0 sourceBody707_113

def sourceBody707_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_0 sourceBody707_114

def sourceBody707_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_0 sourceBody707_115

def sourceBody707_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_0 sourceBody707_116

def sourceBody707_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_0 sourceBody707_117

def sourceBody707_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_0 sourceBody707_118

def sourceBody707_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_0 sourceBody707_119

def sourceBody707_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_63 sourceBody707_120

def sourceBody707_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_35 sourceBody707_121

def sourceBody707_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_0 sourceBody707_122

def sourceBody707_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_34 sourceBody707_123

def sourceBody707_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_0 sourceBody707_124

def sourceBody707_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_33 sourceBody707_125

def sourceBody707_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_0 sourceBody707_126

def sourceBody707_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_32 sourceBody707_127

def sourceBody707_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_0 sourceBody707_128

def sourceBody707_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_31 sourceBody707_129

def sourceBody707_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_0 sourceBody707_130

def sourceBody707_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_30 sourceBody707_131

def sourceBody707_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_0 sourceBody707_132

def sourceBody707_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_29 sourceBody707_133

def sourceBody707_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_0 sourceBody707_134

def sourceBody707_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_0 sourceBody707_135

def sourceBody707_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_0 sourceBody707_136

def sourceBody707_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_0 sourceBody707_137

def sourceBody707_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_0 sourceBody707_138

def sourceBody707_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_0 sourceBody707_139

def sourceBody707_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_0 sourceBody707_140

def sourceBody707_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_0 sourceBody707_141

def sourceBody707_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_0 sourceBody707_142

def sourceBody707_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_0 sourceBody707_143

def sourceBody707_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_0 sourceBody707_144

def sourceBody707_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_0 sourceBody707_145

def sourceBody707_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_0 sourceBody707_146

def sourceBody707_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody707_0 sourceBody707_147

def source707 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (707, 13, sourceBody707_148)
end InitECandidate.Proofs.WordStages
