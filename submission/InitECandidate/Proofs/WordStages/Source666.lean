import InitECandidate.Proofs.WordStages.Source650
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody666_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 2)

def sourceBody666_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody666_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody666_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody666_4 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 24 (Flapjack.WordRegImm.reg 44) sourceBody666_2 sourceBody666_3

def sourceBody666_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody666_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_4 sourceBody666_5

def sourceBody666_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 24)

def sourceBody666_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody666_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.load (Flapjack.WordLangExpHOL.var 6))

def sourceBody666_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody666_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody666_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody666_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.load (Flapjack.WordLangExpHOL.var 8))

def sourceBody666_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody666_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody666_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody666_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 34)

def sourceBody666_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 24)

def sourceBody666_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 44)

def sourceBody666_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 12)

def sourceBody666_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 32)

def sourceBody666_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 22)

def sourceBody666_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 42)

def sourceBody666_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 18)

def sourceBody666_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 30

def sourceBody666_26 : WordLangProgHOL (BitVec 64) :=
.call (some (([38, 28, 48, 10]), ((Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody666_8, 666, 2)) (some 657) ([30, 20, 40, 16, 36, 26, 46, 14]) (some (30, sourceBody666_25, 666, 3))

def sourceBody666_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_26 sourceBody666_5

def sourceBody666_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_27 sourceBody666_8

def sourceBody666_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_24 sourceBody666_28

def sourceBody666_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_23 sourceBody666_29

def sourceBody666_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_22 sourceBody666_30

def sourceBody666_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_21 sourceBody666_31

def sourceBody666_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_20 sourceBody666_32

def sourceBody666_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_19 sourceBody666_33

def sourceBody666_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_18 sourceBody666_34

def sourceBody666_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_17 sourceBody666_35

def sourceBody666_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 4)

def sourceBody666_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 38)

def sourceBody666_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 28)

def sourceBody666_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 48)

def sourceBody666_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 10)

def sourceBody666_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 20)

def sourceBody666_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 30) 26

def sourceBody666_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_43 sourceBody666_8

def sourceBody666_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_42 sourceBody666_44

def sourceBody666_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 40)

def sourceBody666_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 30, Flapjack.WordLangExpHOL.const 8#64])
  26

def sourceBody666_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_47 sourceBody666_8

def sourceBody666_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_46 sourceBody666_48

def sourceBody666_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 16)

def sourceBody666_51 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 30, Flapjack.WordLangExpHOL.const 16#64])
  26

def sourceBody666_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_51 sourceBody666_8

def sourceBody666_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_50 sourceBody666_52

def sourceBody666_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 36)

def sourceBody666_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 30, Flapjack.WordLangExpHOL.const 24#64])
  26

def sourceBody666_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_55 sourceBody666_8

def sourceBody666_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_54 sourceBody666_56

def sourceBody666_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_57 sourceBody666_8

def sourceBody666_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_53 sourceBody666_58

def sourceBody666_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_49 sourceBody666_59

def sourceBody666_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_45 sourceBody666_60

def sourceBody666_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_41 sourceBody666_61

def sourceBody666_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_8 sourceBody666_62

def sourceBody666_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_40 sourceBody666_63

def sourceBody666_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_8 sourceBody666_64

def sourceBody666_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_39 sourceBody666_65

def sourceBody666_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_8 sourceBody666_66

def sourceBody666_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_38 sourceBody666_67

def sourceBody666_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_8 sourceBody666_68

def sourceBody666_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_37 sourceBody666_69

def sourceBody666_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_8 sourceBody666_70

def sourceBody666_72 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody666_73 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [30]

def sourceBody666_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_73 sourceBody666_8

def sourceBody666_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_72 sourceBody666_74

def sourceBody666_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_71 sourceBody666_75

def sourceBody666_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_36 sourceBody666_76

def sourceBody666_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_8 sourceBody666_77

def sourceBody666_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_8 sourceBody666_78

def sourceBody666_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_8 sourceBody666_79

def sourceBody666_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_8 sourceBody666_80

def sourceBody666_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_8 sourceBody666_81

def sourceBody666_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_8 sourceBody666_82

def sourceBody666_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_8 sourceBody666_83

def sourceBody666_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_8 sourceBody666_84

def sourceBody666_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_16 sourceBody666_85

def sourceBody666_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_8 sourceBody666_86

def sourceBody666_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_15 sourceBody666_87

def sourceBody666_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_8 sourceBody666_88

def sourceBody666_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_14 sourceBody666_89

def sourceBody666_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_8 sourceBody666_90

def sourceBody666_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_13 sourceBody666_91

def sourceBody666_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_8 sourceBody666_92

def sourceBody666_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_12 sourceBody666_93

def sourceBody666_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_8 sourceBody666_94

def sourceBody666_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_11 sourceBody666_95

def sourceBody666_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_8 sourceBody666_96

def sourceBody666_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_10 sourceBody666_97

def sourceBody666_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_8 sourceBody666_98

def sourceBody666_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_9 sourceBody666_99

def sourceBody666_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_8 sourceBody666_100

def sourceBody666_102 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.imm 0#64) sourceBody666_101 sourceBody666_8

def sourceBody666_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_102 sourceBody666_5

def sourceBody666_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_103 sourceBody666_8

def sourceBody666_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_7 sourceBody666_104

def sourceBody666_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_6 sourceBody666_105

def sourceBody666_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_1 sourceBody666_106

def sourceBody666_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_0 sourceBody666_107

def sourceBody666_109 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.const 2#64)

def sourceBody666_110 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 4)

def sourceBody666_111 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 6)

def sourceBody666_112 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 8)

def sourceBody666_113 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 24

def sourceBody666_114 : WordLangProgHOL (BitVec 64) :=
.call (some (([34]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody666_8, 666, 4)) (some 662) ([24, 44, 12]) (some (24, sourceBody666_113, 666, 5))

def sourceBody666_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_114 sourceBody666_5

def sourceBody666_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_115 sourceBody666_8

def sourceBody666_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_112 sourceBody666_116

def sourceBody666_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_111 sourceBody666_117

def sourceBody666_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_110 sourceBody666_118

def sourceBody666_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_8 sourceBody666_119

def sourceBody666_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_8 sourceBody666_120

def sourceBody666_122 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody666_123 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [34]

def sourceBody666_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_123 sourceBody666_8

def sourceBody666_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_122 sourceBody666_124

def sourceBody666_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_121 sourceBody666_125

def sourceBody666_127 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.imm 0#64) sourceBody666_126 sourceBody666_8

def sourceBody666_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_127 sourceBody666_5

def sourceBody666_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_128 sourceBody666_8

def sourceBody666_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_7 sourceBody666_129

def sourceBody666_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_6 sourceBody666_130

def sourceBody666_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_109 sourceBody666_131

def sourceBody666_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_0 sourceBody666_132

def sourceBody666_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_108 sourceBody666_133

def sourceBody666_135 : WordLangProgHOL (BitVec 64) :=
.call (some (([34]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody666_8, 666, 6)) (some 664) ([24, 44, 12]) (some (24, sourceBody666_113, 666, 7))

def sourceBody666_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_135 sourceBody666_5

def sourceBody666_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_136 sourceBody666_8

def sourceBody666_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_112 sourceBody666_137

def sourceBody666_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_111 sourceBody666_138

def sourceBody666_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_110 sourceBody666_139

def sourceBody666_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_8 sourceBody666_140

def sourceBody666_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_8 sourceBody666_141

def sourceBody666_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_134 sourceBody666_142

def sourceBody666_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody666_143 sourceBody666_125

def source666 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (666, 5, sourceBody666_144)
end InitECandidate.Proofs.WordStages
