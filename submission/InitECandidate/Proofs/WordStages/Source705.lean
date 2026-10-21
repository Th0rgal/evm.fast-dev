import InitECandidate.Proofs.WordStages.Source689
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody705_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody705_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 60 (Flapjack.WordLangExpHOL.var 2)

def sourceBody705_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.xor
    [Flapjack.WordLangExpHOL.var 14,
      Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
        [Flapjack.WordLangExpHOL.const 0#64, Flapjack.WordLangExpHOL.const 1#64]])

def sourceBody705_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody705_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 1 (Flapjack.WordLangExpHOL.var 44)

def sourceBody705_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.addCarry 3 60 26 1))

def sourceBody705_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 1)

def sourceBody705_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 3)

def sourceBody705_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_6 sourceBody705_7

def sourceBody705_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_5 sourceBody705_8

def sourceBody705_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_4 sourceBody705_9

def sourceBody705_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_3 sourceBody705_10

def sourceBody705_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_0 sourceBody705_11

def sourceBody705_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_2 sourceBody705_12

def sourceBody705_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_0 sourceBody705_13

def sourceBody705_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_1 sourceBody705_14

def sourceBody705_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_0 sourceBody705_15

def sourceBody705_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 4)

def sourceBody705_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.xor
    [Flapjack.WordLangExpHOL.var 16,
      Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
        [Flapjack.WordLangExpHOL.const 0#64, Flapjack.WordLangExpHOL.const 1#64]])

def sourceBody705_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 40)

def sourceBody705_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 1 (Flapjack.WordLangExpHOL.var 54)

def sourceBody705_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.addCarry 3 44 34 1))

def sourceBody705_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 1)

def sourceBody705_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 60 (Flapjack.WordLangExpHOL.var 3)

def sourceBody705_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_22 sourceBody705_23

def sourceBody705_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_21 sourceBody705_24

def sourceBody705_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_20 sourceBody705_25

def sourceBody705_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_19 sourceBody705_26

def sourceBody705_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_0 sourceBody705_27

def sourceBody705_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_18 sourceBody705_28

def sourceBody705_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_0 sourceBody705_29

def sourceBody705_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_17 sourceBody705_30

def sourceBody705_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_0 sourceBody705_31

def sourceBody705_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 6)

def sourceBody705_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.xor
    [Flapjack.WordLangExpHOL.var 18,
      Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
        [Flapjack.WordLangExpHOL.const 0#64, Flapjack.WordLangExpHOL.const 1#64]])

def sourceBody705_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 26)

def sourceBody705_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 1 (Flapjack.WordLangExpHOL.var 48)

def sourceBody705_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.addCarry 3 54 30 1))

def sourceBody705_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 1)

def sourceBody705_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 3)

def sourceBody705_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_38 sourceBody705_39

def sourceBody705_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_37 sourceBody705_40

def sourceBody705_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_36 sourceBody705_41

def sourceBody705_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_35 sourceBody705_42

def sourceBody705_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_0 sourceBody705_43

def sourceBody705_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_34 sourceBody705_44

def sourceBody705_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_0 sourceBody705_45

def sourceBody705_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_33 sourceBody705_46

def sourceBody705_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_0 sourceBody705_47

def sourceBody705_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 8)

def sourceBody705_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.xor
    [Flapjack.WordLangExpHOL.var 20,
      Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
        [Flapjack.WordLangExpHOL.const 0#64, Flapjack.WordLangExpHOL.const 1#64]])

def sourceBody705_51 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.var 34)

def sourceBody705_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 1 (Flapjack.WordLangExpHOL.var 58)

def sourceBody705_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.addCarry 3 48 38 1))

def sourceBody705_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 1)

def sourceBody705_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 3)

def sourceBody705_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_54 sourceBody705_55

def sourceBody705_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_53 sourceBody705_56

def sourceBody705_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_52 sourceBody705_57

def sourceBody705_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_51 sourceBody705_58

def sourceBody705_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_0 sourceBody705_59

def sourceBody705_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_50 sourceBody705_60

def sourceBody705_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_0 sourceBody705_61

def sourceBody705_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_49 sourceBody705_62

def sourceBody705_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_0 sourceBody705_63

def sourceBody705_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.var 10)

def sourceBody705_66 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.xor
    [Flapjack.WordLangExpHOL.var 22,
      Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
        [Flapjack.WordLangExpHOL.const 0#64, Flapjack.WordLangExpHOL.const 1#64]])

def sourceBody705_67 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 30)

def sourceBody705_68 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 1 (Flapjack.WordLangExpHOL.var 46)

def sourceBody705_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.addCarry 3 58 28 1))

def sourceBody705_70 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 1)

def sourceBody705_71 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 3)

def sourceBody705_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_70 sourceBody705_71

def sourceBody705_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_69 sourceBody705_72

def sourceBody705_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_68 sourceBody705_73

def sourceBody705_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_67 sourceBody705_74

def sourceBody705_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_0 sourceBody705_75

def sourceBody705_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_66 sourceBody705_76

def sourceBody705_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_0 sourceBody705_77

def sourceBody705_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_65 sourceBody705_78

def sourceBody705_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_0 sourceBody705_79

def sourceBody705_81 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 12)

def sourceBody705_82 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.xor
    [Flapjack.WordLangExpHOL.var 24,
      Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
        [Flapjack.WordLangExpHOL.const 0#64, Flapjack.WordLangExpHOL.const 1#64]])

def sourceBody705_83 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.var 38)

def sourceBody705_84 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 1 (Flapjack.WordLangExpHOL.var 56)

def sourceBody705_85 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.addCarry 3 46 36 1))

def sourceBody705_86 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 1)

def sourceBody705_87 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.var 3)

def sourceBody705_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_86 sourceBody705_87

def sourceBody705_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_85 sourceBody705_88

def sourceBody705_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_84 sourceBody705_89

def sourceBody705_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_83 sourceBody705_90

def sourceBody705_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_0 sourceBody705_91

def sourceBody705_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_82 sourceBody705_92

def sourceBody705_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_0 sourceBody705_93

def sourceBody705_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_81 sourceBody705_94

def sourceBody705_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_0 sourceBody705_95

def sourceBody705_97 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 50)

def sourceBody705_98 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 60)

def sourceBody705_99 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.var 44)

def sourceBody705_100 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 54)

def sourceBody705_101 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.var 48)

def sourceBody705_102 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 58)

def sourceBody705_103 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 62 (Flapjack.WordLangExpHOL.var 28)

def sourceBody705_104 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [46, 36, 56, 32, 52, 42, 62]

def sourceBody705_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_104 sourceBody705_0

def sourceBody705_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_103 sourceBody705_105

def sourceBody705_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_102 sourceBody705_106

def sourceBody705_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_101 sourceBody705_107

def sourceBody705_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_100 sourceBody705_108

def sourceBody705_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_99 sourceBody705_109

def sourceBody705_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_98 sourceBody705_110

def sourceBody705_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_97 sourceBody705_111

def sourceBody705_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_96 sourceBody705_112

def sourceBody705_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_0 sourceBody705_113

def sourceBody705_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_0 sourceBody705_114

def sourceBody705_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_0 sourceBody705_115

def sourceBody705_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_0 sourceBody705_116

def sourceBody705_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_80 sourceBody705_117

def sourceBody705_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_0 sourceBody705_118

def sourceBody705_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_0 sourceBody705_119

def sourceBody705_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_0 sourceBody705_120

def sourceBody705_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_0 sourceBody705_121

def sourceBody705_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_64 sourceBody705_122

def sourceBody705_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_0 sourceBody705_123

def sourceBody705_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_0 sourceBody705_124

def sourceBody705_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_0 sourceBody705_125

def sourceBody705_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_0 sourceBody705_126

def sourceBody705_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_48 sourceBody705_127

def sourceBody705_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_0 sourceBody705_128

def sourceBody705_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_0 sourceBody705_129

def sourceBody705_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_0 sourceBody705_130

def sourceBody705_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_0 sourceBody705_131

def sourceBody705_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_32 sourceBody705_132

def sourceBody705_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_0 sourceBody705_133

def sourceBody705_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_0 sourceBody705_134

def sourceBody705_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_0 sourceBody705_135

def sourceBody705_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_0 sourceBody705_136

def sourceBody705_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_16 sourceBody705_137

def sourceBody705_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_0 sourceBody705_138

def sourceBody705_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_0 sourceBody705_139

def sourceBody705_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_0 sourceBody705_140

def sourceBody705_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody705_0 sourceBody705_141

def source705 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (705, 13, sourceBody705_142)
end InitECandidate.Proofs.WordStages
