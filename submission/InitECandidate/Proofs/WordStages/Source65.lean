import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody65_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody65_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 22

def sourceBody65_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody65_0, 65, 2)) (some 67) ([]) (some (22, sourceBody65_1, 65, 3))

def sourceBody65_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody65_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_2 sourceBody65_3

def sourceBody65_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_4 sourceBody65_0

def sourceBody65_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_0 sourceBody65_5

def sourceBody65_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_0 sourceBody65_6

def sourceBody65_8 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody65_0, 65, 4)) (some 149) ([]) (some (22, sourceBody65_1, 65, 5))

def sourceBody65_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_8 sourceBody65_3

def sourceBody65_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_9 sourceBody65_0

def sourceBody65_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_0 sourceBody65_10

def sourceBody65_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_0 sourceBody65_11

def sourceBody65_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_7 sourceBody65_12

def sourceBody65_14 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody65_0, 65, 6)) (some 155) ([]) (some (22, sourceBody65_1, 65, 7))

def sourceBody65_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_14 sourceBody65_3

def sourceBody65_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_15 sourceBody65_0

def sourceBody65_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_0 sourceBody65_16

def sourceBody65_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_0 sourceBody65_17

def sourceBody65_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_13 sourceBody65_18

def sourceBody65_20 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody65_0, 65, 8)) (some 234) ([]) (some (22, sourceBody65_1, 65, 9))

def sourceBody65_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_20 sourceBody65_3

def sourceBody65_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_21 sourceBody65_0

def sourceBody65_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_0 sourceBody65_22

def sourceBody65_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_0 sourceBody65_23

def sourceBody65_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_19 sourceBody65_24

def sourceBody65_26 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody65_0, 65, 10)) (some 283) ([]) (some (22, sourceBody65_1, 65, 11))

def sourceBody65_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_26 sourceBody65_3

def sourceBody65_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_27 sourceBody65_0

def sourceBody65_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_0 sourceBody65_28

def sourceBody65_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_0 sourceBody65_29

def sourceBody65_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_25 sourceBody65_30

def sourceBody65_32 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody65_0, 65, 12)) (some 98) ([]) (some (22, sourceBody65_1, 65, 13))

def sourceBody65_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_32 sourceBody65_3

def sourceBody65_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_33 sourceBody65_0

def sourceBody65_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_0 sourceBody65_34

def sourceBody65_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_0 sourceBody65_35

def sourceBody65_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_31 sourceBody65_36

def sourceBody65_38 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody65_0, 65, 14)) (some 201) ([]) (some (22, sourceBody65_1, 65, 15))

def sourceBody65_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_38 sourceBody65_3

def sourceBody65_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_39 sourceBody65_0

def sourceBody65_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_0 sourceBody65_40

def sourceBody65_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_0 sourceBody65_41

def sourceBody65_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_37 sourceBody65_42

def sourceBody65_44 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody65_0, 65, 16)) (some 653) ([]) (some (22, sourceBody65_1, 65, 17))

def sourceBody65_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_44 sourceBody65_3

def sourceBody65_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_45 sourceBody65_0

def sourceBody65_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_0 sourceBody65_46

def sourceBody65_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_0 sourceBody65_47

def sourceBody65_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_43 sourceBody65_48

def sourceBody65_50 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody65_0, 65, 18)) (some 814) ([]) (some (22, sourceBody65_1, 65, 19))

def sourceBody65_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_50 sourceBody65_3

def sourceBody65_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_51 sourceBody65_0

def sourceBody65_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_0 sourceBody65_52

def sourceBody65_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_0 sourceBody65_53

def sourceBody65_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_49 sourceBody65_54

def sourceBody65_56 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody65_0, 65, 20)) (some 622) ([]) (some (22, sourceBody65_1, 65, 21))

def sourceBody65_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_56 sourceBody65_3

def sourceBody65_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_57 sourceBody65_0

def sourceBody65_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_0 sourceBody65_58

def sourceBody65_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_0 sourceBody65_59

def sourceBody65_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_55 sourceBody65_60

def sourceBody65_62 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody65_0, 65, 22)) (some 628) ([]) (some (22, sourceBody65_1, 65, 23))

def sourceBody65_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_62 sourceBody65_3

def sourceBody65_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_63 sourceBody65_0

def sourceBody65_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_0 sourceBody65_64

def sourceBody65_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_0 sourceBody65_65

def sourceBody65_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_61 sourceBody65_66

def sourceBody65_68 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody65_0, 65, 24)) (some 280) ([]) (some (22, sourceBody65_1, 65, 25))

def sourceBody65_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_68 sourceBody65_3

def sourceBody65_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_69 sourceBody65_0

def sourceBody65_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_0 sourceBody65_70

def sourceBody65_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_0 sourceBody65_71

def sourceBody65_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_67 sourceBody65_72

def sourceBody65_74 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody65_0, 65, 26)) (some 580) ([]) (some (22, sourceBody65_1, 65, 27))

def sourceBody65_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_74 sourceBody65_3

def sourceBody65_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_75 sourceBody65_0

def sourceBody65_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_0 sourceBody65_76

def sourceBody65_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_0 sourceBody65_77

def sourceBody65_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_73 sourceBody65_78

def sourceBody65_80 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody65_0, 65, 28)) (some 848) ([]) (some (22, sourceBody65_1, 65, 29))

def sourceBody65_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_80 sourceBody65_3

def sourceBody65_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_81 sourceBody65_0

def sourceBody65_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_0 sourceBody65_82

def sourceBody65_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_0 sourceBody65_83

def sourceBody65_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_79 sourceBody65_84

def sourceBody65_86 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 4

def sourceBody65_87 : WordLangProgHOL (BitVec 64) :=
.call (some (([8, 22]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody65_0, 65, 30)) (some 90) ([]) (some (4, sourceBody65_86, 65, 31))

def sourceBody65_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_87 sourceBody65_3

def sourceBody65_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_88 sourceBody65_0

def sourceBody65_90 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 256#64)

def sourceBody65_91 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody65_92 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody65_0, 65, 32)) (some 68) ([18]) (some (18, sourceBody65_91, 65, 33))

def sourceBody65_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_92 sourceBody65_3

def sourceBody65_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_93 sourceBody65_0

def sourceBody65_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_90 sourceBody65_94

def sourceBody65_96 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody65_97 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody65_98 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody65_0, 65, 34)) (some 68) ([12]) (some (12, sourceBody65_97, 65, 35))

def sourceBody65_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_98 sourceBody65_3

def sourceBody65_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_99 sourceBody65_0

def sourceBody65_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_96 sourceBody65_100

def sourceBody65_102 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 18)

def sourceBody65_103 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody65_104 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 26

def sourceBody65_105 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody65_0, 65, 36)) (some 78) ([26, 2]) (some (26, sourceBody65_104, 65, 37))

def sourceBody65_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_105 sourceBody65_3

def sourceBody65_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_106 sourceBody65_0

def sourceBody65_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_103 sourceBody65_107

def sourceBody65_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_102 sourceBody65_108

def sourceBody65_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_0 sourceBody65_109

def sourceBody65_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_0 sourceBody65_110

def sourceBody65_112 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 8)

def sourceBody65_113 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 22)

def sourceBody65_114 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 2

def sourceBody65_115 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.lookup (Flapjack.WordStore.temp 0#5))

def sourceBody65_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_115 sourceBody65_0

def sourceBody65_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_116 sourceBody65_0

def sourceBody65_118 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 4)

def sourceBody65_119 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 18)

def sourceBody65_120 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody65_121 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody65_122 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody65_123 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody65_124 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody65_0, 65, 39)) (some 264) ([16, 10, 24, 6, 20]) (some (16, sourceBody65_123, 65, 40))

def sourceBody65_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_124 sourceBody65_3

def sourceBody65_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_125 sourceBody65_0

def sourceBody65_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_122 sourceBody65_126

def sourceBody65_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_121 sourceBody65_127

def sourceBody65_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_120 sourceBody65_128

def sourceBody65_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_119 sourceBody65_129

def sourceBody65_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_118 sourceBody65_130

def sourceBody65_132 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.var 2])

def sourceBody65_133 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 26)

def sourceBody65_134 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.store8 10 (Flapjack.WordLangAddr.addr 16 0#64))

def sourceBody65_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_134 sourceBody65_0

def sourceBody65_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_133 sourceBody65_135

def sourceBody65_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_132 sourceBody65_136

def sourceBody65_138 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 4)

def sourceBody65_139 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody65_140 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody65_141 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody65_0, 65, 41)) (some 91) ([10, 24]) (some (10, sourceBody65_140, 65, 42))

def sourceBody65_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_141 sourceBody65_3

def sourceBody65_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_142 sourceBody65_0

def sourceBody65_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_139 sourceBody65_143

def sourceBody65_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_138 sourceBody65_144

def sourceBody65_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_0 sourceBody65_145

def sourceBody65_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_0 sourceBody65_146

def sourceBody65_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_137 sourceBody65_147

def sourceBody65_149 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap)

def sourceBody65_150 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody65_151 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap)

def sourceBody65_152 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.ffi (Flapjack.Basis.Pure.MlString.MlString.implode [104#8, 97#8, 108#8, 116#8]) 16 10 24 6
  (Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)

def sourceBody65_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_121 sourceBody65_152

def sourceBody65_154 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_0 sourceBody65_153

def sourceBody65_155 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_151 sourceBody65_154

def sourceBody65_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_0 sourceBody65_155

def sourceBody65_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_150 sourceBody65_156

def sourceBody65_158 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_0 sourceBody65_157

def sourceBody65_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_149 sourceBody65_158

def sourceBody65_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_0 sourceBody65_159

def sourceBody65_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_148 sourceBody65_160

def sourceBody65_162 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody65_163 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [16]

def sourceBody65_164 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_163 sourceBody65_0

def sourceBody65_165 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_162 sourceBody65_164

def sourceBody65_166 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_161 sourceBody65_165

def sourceBody65_167 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_131 sourceBody65_166

def sourceBody65_168 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_0 sourceBody65_167

def sourceBody65_169 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_0 sourceBody65_168

def sourceBody65_170 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_117 sourceBody65_169

def sourceBody65_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_3 sourceBody65_170

def sourceBody65_172 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 2 (Flapjack.WordRegImm.imm 2#64) sourceBody65_114 sourceBody65_171

def sourceBody65_173 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_172 sourceBody65_3

def sourceBody65_174 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody65_0, 65, 38)) (some 252) ([2, 16]) (some (2, sourceBody65_173, 65, 43))

def sourceBody65_175 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_174 sourceBody65_3

def sourceBody65_176 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_175 sourceBody65_0

def sourceBody65_177 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_113 sourceBody65_176

def sourceBody65_178 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_112 sourceBody65_177

def sourceBody65_179 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody65_180 : WordLangProgHOL (BitVec 64) :=
.call (some (([2]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody65_0, 65, 44)) (some 68) ([16]) (some (16, sourceBody65_123, 65, 45))

def sourceBody65_181 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_180 sourceBody65_3

def sourceBody65_182 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_181 sourceBody65_0

def sourceBody65_183 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_179 sourceBody65_182

def sourceBody65_184 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 12)

def sourceBody65_185 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 2)

def sourceBody65_186 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody65_0, 65, 46)) (some 263) ([10, 24]) (some (10, sourceBody65_140, 65, 47))

def sourceBody65_187 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_186 sourceBody65_3

def sourceBody65_188 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_187 sourceBody65_0

def sourceBody65_189 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_185 sourceBody65_188

def sourceBody65_190 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_184 sourceBody65_189

def sourceBody65_191 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_0 sourceBody65_190

def sourceBody65_192 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_0 sourceBody65_191

def sourceBody65_193 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody65_0, 65, 48)) (some 873) ([10]) (some (10, sourceBody65_140, 65, 49))

def sourceBody65_194 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_193 sourceBody65_3

def sourceBody65_195 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_194 sourceBody65_0

def sourceBody65_196 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_184 sourceBody65_195

def sourceBody65_197 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 4)

def sourceBody65_198 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 2)

def sourceBody65_199 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 16)

def sourceBody65_200 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 88#64]))

def sourceBody65_201 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 5377#64)

def sourceBody65_202 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 24

def sourceBody65_203 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody65_0, 65, 50)) (some 264) ([24, 6, 20, 14, 28]) (some (24, sourceBody65_202, 65, 51))

def sourceBody65_204 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_203 sourceBody65_3

def sourceBody65_205 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_204 sourceBody65_0

def sourceBody65_206 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_201 sourceBody65_205

def sourceBody65_207 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_200 sourceBody65_206

def sourceBody65_208 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_199 sourceBody65_207

def sourceBody65_209 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_198 sourceBody65_208

def sourceBody65_210 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_197 sourceBody65_209

def sourceBody65_211 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.var 10])

def sourceBody65_212 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 536#64]))

def sourceBody65_213 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.store8 6 (Flapjack.WordLangAddr.addr 24 0#64))

def sourceBody65_214 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_213 sourceBody65_0

def sourceBody65_215 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_212 sourceBody65_214

def sourceBody65_216 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_211 sourceBody65_215

def sourceBody65_217 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 4)

def sourceBody65_218 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody65_219 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody65_220 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody65_0, 65, 52)) (some 91) ([6, 20]) (some (6, sourceBody65_219, 65, 53))

def sourceBody65_221 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_220 sourceBody65_3

def sourceBody65_222 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_221 sourceBody65_0

def sourceBody65_223 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_218 sourceBody65_222

def sourceBody65_224 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_217 sourceBody65_223

def sourceBody65_225 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_0 sourceBody65_224

def sourceBody65_226 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_0 sourceBody65_225

def sourceBody65_227 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_216 sourceBody65_226

def sourceBody65_228 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap)

def sourceBody65_229 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody65_230 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.ffi (Flapjack.Basis.Pure.MlString.MlString.implode [104#8, 97#8, 108#8, 116#8]) 24 6 20 14
  (Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)

def sourceBody65_231 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_229 sourceBody65_230

def sourceBody65_232 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_0 sourceBody65_231

def sourceBody65_233 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_228 sourceBody65_232

def sourceBody65_234 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_0 sourceBody65_233

def sourceBody65_235 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_121 sourceBody65_234

def sourceBody65_236 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_0 sourceBody65_235

def sourceBody65_237 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_151 sourceBody65_236

def sourceBody65_238 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_0 sourceBody65_237

def sourceBody65_239 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_227 sourceBody65_238

def sourceBody65_240 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [24]

def sourceBody65_241 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_240 sourceBody65_0

def sourceBody65_242 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_120 sourceBody65_241

def sourceBody65_243 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_239 sourceBody65_242

def sourceBody65_244 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_210 sourceBody65_243

def sourceBody65_245 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_0 sourceBody65_244

def sourceBody65_246 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_0 sourceBody65_245

def sourceBody65_247 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_196 sourceBody65_246

def sourceBody65_248 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_0 sourceBody65_247

def sourceBody65_249 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_0 sourceBody65_248

def sourceBody65_250 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_192 sourceBody65_249

def sourceBody65_251 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_183 sourceBody65_250

def sourceBody65_252 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_0 sourceBody65_251

def sourceBody65_253 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_0 sourceBody65_252

def sourceBody65_254 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_178 sourceBody65_253

def sourceBody65_255 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_0 sourceBody65_254

def sourceBody65_256 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_0 sourceBody65_255

def sourceBody65_257 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_0 sourceBody65_256

def sourceBody65_258 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_0 sourceBody65_257

def sourceBody65_259 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_111 sourceBody65_258

def sourceBody65_260 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_101 sourceBody65_259

def sourceBody65_261 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_0 sourceBody65_260

def sourceBody65_262 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_0 sourceBody65_261

def sourceBody65_263 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_95 sourceBody65_262

def sourceBody65_264 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_0 sourceBody65_263

def sourceBody65_265 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_0 sourceBody65_264

def sourceBody65_266 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_89 sourceBody65_265

def sourceBody65_267 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_0 sourceBody65_266

def sourceBody65_268 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_0 sourceBody65_267

def sourceBody65_269 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_0 sourceBody65_268

def sourceBody65_270 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_0 sourceBody65_269

def sourceBody65_271 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody65_85 sourceBody65_270

def source65 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
(65, 1, sourceBody65_271)
end InitECandidate.Proofs.WordStages
