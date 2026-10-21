import InitECandidate.Proofs.WordStages.Source688
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody704_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody704_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 60 (Flapjack.WordLangExpHOL.var 2)

def sourceBody704_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 14)

def sourceBody704_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody704_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 1 (Flapjack.WordLangExpHOL.var 44)

def sourceBody704_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.addCarry 3 60 26 1))

def sourceBody704_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 1)

def sourceBody704_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 3)

def sourceBody704_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_6 sourceBody704_7

def sourceBody704_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_5 sourceBody704_8

def sourceBody704_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_4 sourceBody704_9

def sourceBody704_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_3 sourceBody704_10

def sourceBody704_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_0 sourceBody704_11

def sourceBody704_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_2 sourceBody704_12

def sourceBody704_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_0 sourceBody704_13

def sourceBody704_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_1 sourceBody704_14

def sourceBody704_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_0 sourceBody704_15

def sourceBody704_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 4)

def sourceBody704_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 16)

def sourceBody704_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 40)

def sourceBody704_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 1 (Flapjack.WordLangExpHOL.var 54)

def sourceBody704_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.addCarry 3 44 34 1))

def sourceBody704_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 1)

def sourceBody704_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 60 (Flapjack.WordLangExpHOL.var 3)

def sourceBody704_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_22 sourceBody704_23

def sourceBody704_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_21 sourceBody704_24

def sourceBody704_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_20 sourceBody704_25

def sourceBody704_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_19 sourceBody704_26

def sourceBody704_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_0 sourceBody704_27

def sourceBody704_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_18 sourceBody704_28

def sourceBody704_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_0 sourceBody704_29

def sourceBody704_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_17 sourceBody704_30

def sourceBody704_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_0 sourceBody704_31

def sourceBody704_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 6)

def sourceBody704_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 18)

def sourceBody704_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 26)

def sourceBody704_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 1 (Flapjack.WordLangExpHOL.var 48)

def sourceBody704_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.addCarry 3 54 30 1))

def sourceBody704_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 1)

def sourceBody704_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 3)

def sourceBody704_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_38 sourceBody704_39

def sourceBody704_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_37 sourceBody704_40

def sourceBody704_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_36 sourceBody704_41

def sourceBody704_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_35 sourceBody704_42

def sourceBody704_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_0 sourceBody704_43

def sourceBody704_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_34 sourceBody704_44

def sourceBody704_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_0 sourceBody704_45

def sourceBody704_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_33 sourceBody704_46

def sourceBody704_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_0 sourceBody704_47

def sourceBody704_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 8)

def sourceBody704_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 20)

def sourceBody704_51 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.var 34)

def sourceBody704_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 1 (Flapjack.WordLangExpHOL.var 58)

def sourceBody704_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.addCarry 3 48 38 1))

def sourceBody704_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 1)

def sourceBody704_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 3)

def sourceBody704_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_54 sourceBody704_55

def sourceBody704_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_53 sourceBody704_56

def sourceBody704_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_52 sourceBody704_57

def sourceBody704_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_51 sourceBody704_58

def sourceBody704_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_0 sourceBody704_59

def sourceBody704_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_50 sourceBody704_60

def sourceBody704_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_0 sourceBody704_61

def sourceBody704_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_49 sourceBody704_62

def sourceBody704_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_0 sourceBody704_63

def sourceBody704_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.var 10)

def sourceBody704_66 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 22)

def sourceBody704_67 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 30)

def sourceBody704_68 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 1 (Flapjack.WordLangExpHOL.var 46)

def sourceBody704_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.addCarry 3 58 28 1))

def sourceBody704_70 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 1)

def sourceBody704_71 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 3)

def sourceBody704_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_70 sourceBody704_71

def sourceBody704_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_69 sourceBody704_72

def sourceBody704_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_68 sourceBody704_73

def sourceBody704_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_67 sourceBody704_74

def sourceBody704_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_0 sourceBody704_75

def sourceBody704_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_66 sourceBody704_76

def sourceBody704_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_0 sourceBody704_77

def sourceBody704_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_65 sourceBody704_78

def sourceBody704_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_0 sourceBody704_79

def sourceBody704_81 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 12)

def sourceBody704_82 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 24)

def sourceBody704_83 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.var 38)

def sourceBody704_84 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 1 (Flapjack.WordLangExpHOL.var 56)

def sourceBody704_85 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.addCarry 3 46 36 1))

def sourceBody704_86 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 1)

def sourceBody704_87 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.var 3)

def sourceBody704_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_86 sourceBody704_87

def sourceBody704_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_85 sourceBody704_88

def sourceBody704_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_84 sourceBody704_89

def sourceBody704_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_83 sourceBody704_90

def sourceBody704_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_0 sourceBody704_91

def sourceBody704_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_82 sourceBody704_92

def sourceBody704_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_0 sourceBody704_93

def sourceBody704_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_81 sourceBody704_94

def sourceBody704_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_0 sourceBody704_95

def sourceBody704_97 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 50)

def sourceBody704_98 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 60)

def sourceBody704_99 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.var 44)

def sourceBody704_100 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 54)

def sourceBody704_101 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.var 48)

def sourceBody704_102 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 58)

def sourceBody704_103 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 62 (Flapjack.WordLangExpHOL.var 28)

def sourceBody704_104 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [46, 36, 56, 32, 52, 42, 62]

def sourceBody704_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_104 sourceBody704_0

def sourceBody704_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_103 sourceBody704_105

def sourceBody704_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_102 sourceBody704_106

def sourceBody704_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_101 sourceBody704_107

def sourceBody704_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_100 sourceBody704_108

def sourceBody704_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_99 sourceBody704_109

def sourceBody704_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_98 sourceBody704_110

def sourceBody704_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_97 sourceBody704_111

def sourceBody704_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_96 sourceBody704_112

def sourceBody704_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_0 sourceBody704_113

def sourceBody704_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_0 sourceBody704_114

def sourceBody704_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_0 sourceBody704_115

def sourceBody704_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_0 sourceBody704_116

def sourceBody704_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_80 sourceBody704_117

def sourceBody704_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_0 sourceBody704_118

def sourceBody704_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_0 sourceBody704_119

def sourceBody704_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_0 sourceBody704_120

def sourceBody704_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_0 sourceBody704_121

def sourceBody704_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_64 sourceBody704_122

def sourceBody704_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_0 sourceBody704_123

def sourceBody704_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_0 sourceBody704_124

def sourceBody704_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_0 sourceBody704_125

def sourceBody704_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_0 sourceBody704_126

def sourceBody704_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_48 sourceBody704_127

def sourceBody704_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_0 sourceBody704_128

def sourceBody704_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_0 sourceBody704_129

def sourceBody704_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_0 sourceBody704_130

def sourceBody704_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_0 sourceBody704_131

def sourceBody704_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_32 sourceBody704_132

def sourceBody704_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_0 sourceBody704_133

def sourceBody704_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_0 sourceBody704_134

def sourceBody704_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_0 sourceBody704_135

def sourceBody704_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_0 sourceBody704_136

def sourceBody704_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_16 sourceBody704_137

def sourceBody704_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_0 sourceBody704_138

def sourceBody704_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_0 sourceBody704_139

def sourceBody704_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_0 sourceBody704_140

def sourceBody704_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody704_0 sourceBody704_141

def source704 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (704, 13, sourceBody704_142)
end InitECandidate.Proofs.WordStages
