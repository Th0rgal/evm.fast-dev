import InitECandidate.Proofs.WordStages.Source564
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody580_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody580_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody580_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody580_0, 580, 2)) (some 69) ([]) (some (12, sourceBody580_1, 580, 3))

def sourceBody580_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody580_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_2 sourceBody580_3

def sourceBody580_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_4 sourceBody580_0

def sourceBody580_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 40#64)

def sourceBody580_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 4

def sourceBody580_8 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody580_0, 580, 4)) (some 68) ([4]) (some (4, sourceBody580_7, 580, 5))

def sourceBody580_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_8 sourceBody580_3

def sourceBody580_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_9 sourceBody580_0

def sourceBody580_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_6 sourceBody580_10

def sourceBody580_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 12)

def sourceBody580_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 84#64)

def sourceBody580_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.store8 10 (Flapjack.WordLangAddr.addr 4 0#64))

def sourceBody580_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_14 sourceBody580_0

def sourceBody580_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_13 sourceBody580_15

def sourceBody580_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_12 sourceBody580_16

def sourceBody580_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody580_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 114#64)

def sourceBody580_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_19 sourceBody580_15

def sourceBody580_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_18 sourceBody580_20

def sourceBody580_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_17 sourceBody580_21

def sourceBody580_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 2#64])

def sourceBody580_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 97#64)

def sourceBody580_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_24 sourceBody580_15

def sourceBody580_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_23 sourceBody580_25

def sourceBody580_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_22 sourceBody580_26

def sourceBody580_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 3#64])

def sourceBody580_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 110#64)

def sourceBody580_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_29 sourceBody580_15

def sourceBody580_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_28 sourceBody580_30

def sourceBody580_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_27 sourceBody580_31

def sourceBody580_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 4#64])

def sourceBody580_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 115#64)

def sourceBody580_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_34 sourceBody580_15

def sourceBody580_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_33 sourceBody580_35

def sourceBody580_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_32 sourceBody580_36

def sourceBody580_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 5#64])

def sourceBody580_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 102#64)

def sourceBody580_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_39 sourceBody580_15

def sourceBody580_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_38 sourceBody580_40

def sourceBody580_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_37 sourceBody580_41

def sourceBody580_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 6#64])

def sourceBody580_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 101#64)

def sourceBody580_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_44 sourceBody580_15

def sourceBody580_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_43 sourceBody580_45

def sourceBody580_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_42 sourceBody580_46

def sourceBody580_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 7#64])

def sourceBody580_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_48 sourceBody580_20

def sourceBody580_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_47 sourceBody580_49

def sourceBody580_51 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 8#64])

def sourceBody580_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 40#64)

def sourceBody580_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_52 sourceBody580_15

def sourceBody580_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_51 sourceBody580_53

def sourceBody580_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_50 sourceBody580_54

def sourceBody580_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 9#64])

def sourceBody580_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_56 sourceBody580_25

def sourceBody580_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_55 sourceBody580_57

def sourceBody580_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 10#64])

def sourceBody580_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 100#64)

def sourceBody580_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_60 sourceBody580_15

def sourceBody580_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_59 sourceBody580_61

def sourceBody580_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_58 sourceBody580_62

def sourceBody580_64 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 11#64])

def sourceBody580_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_64 sourceBody580_61

def sourceBody580_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_63 sourceBody580_65

def sourceBody580_67 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 12#64])

def sourceBody580_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_67 sourceBody580_20

def sourceBody580_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_66 sourceBody580_68

def sourceBody580_70 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 13#64])

def sourceBody580_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_70 sourceBody580_45

def sourceBody580_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_69 sourceBody580_71

def sourceBody580_73 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 14#64])

def sourceBody580_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_73 sourceBody580_35

def sourceBody580_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_72 sourceBody580_74

def sourceBody580_76 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 15#64])

def sourceBody580_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_76 sourceBody580_35

def sourceBody580_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_75 sourceBody580_77

def sourceBody580_79 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 16#64])

def sourceBody580_80 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 44#64)

def sourceBody580_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_80 sourceBody580_15

def sourceBody580_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_79 sourceBody580_81

def sourceBody580_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_78 sourceBody580_82

def sourceBody580_84 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 17#64])

def sourceBody580_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_84 sourceBody580_25

def sourceBody580_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_83 sourceBody580_85

def sourceBody580_87 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 18#64])

def sourceBody580_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_87 sourceBody580_61

def sourceBody580_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_86 sourceBody580_88

def sourceBody580_90 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 19#64])

def sourceBody580_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_90 sourceBody580_61

def sourceBody580_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_89 sourceBody580_91

def sourceBody580_93 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 20#64])

def sourceBody580_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_93 sourceBody580_20

def sourceBody580_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_92 sourceBody580_94

def sourceBody580_96 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 21#64])

def sourceBody580_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_96 sourceBody580_45

def sourceBody580_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_95 sourceBody580_97

def sourceBody580_99 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 22#64])

def sourceBody580_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_99 sourceBody580_35

def sourceBody580_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_98 sourceBody580_100

def sourceBody580_102 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 23#64])

def sourceBody580_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_102 sourceBody580_35

def sourceBody580_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_101 sourceBody580_103

def sourceBody580_105 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 24#64])

def sourceBody580_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_105 sourceBody580_81

def sourceBody580_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_104 sourceBody580_106

def sourceBody580_108 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 25#64])

def sourceBody580_109 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 117#64)

def sourceBody580_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_109 sourceBody580_15

def sourceBody580_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_108 sourceBody580_110

def sourceBody580_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_107 sourceBody580_111

def sourceBody580_113 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 26#64])

def sourceBody580_114 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 105#64)

def sourceBody580_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_114 sourceBody580_15

def sourceBody580_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_113 sourceBody580_115

def sourceBody580_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_112 sourceBody580_116

def sourceBody580_118 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 27#64])

def sourceBody580_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_118 sourceBody580_30

def sourceBody580_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_117 sourceBody580_119

def sourceBody580_121 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 28#64])

def sourceBody580_122 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 116#64)

def sourceBody580_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_122 sourceBody580_15

def sourceBody580_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_121 sourceBody580_123

def sourceBody580_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_120 sourceBody580_124

def sourceBody580_126 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 29#64])

def sourceBody580_127 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 50#64)

def sourceBody580_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_127 sourceBody580_15

def sourceBody580_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_126 sourceBody580_128

def sourceBody580_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_125 sourceBody580_129

def sourceBody580_131 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 30#64])

def sourceBody580_132 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 53#64)

def sourceBody580_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_132 sourceBody580_15

def sourceBody580_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_131 sourceBody580_133

def sourceBody580_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_130 sourceBody580_134

def sourceBody580_136 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 31#64])

def sourceBody580_137 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 54#64)

def sourceBody580_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_137 sourceBody580_15

def sourceBody580_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_136 sourceBody580_138

def sourceBody580_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_135 sourceBody580_139

def sourceBody580_141 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 32#64])

def sourceBody580_142 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 41#64)

def sourceBody580_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_142 sourceBody580_15

def sourceBody580_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_141 sourceBody580_143

def sourceBody580_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_140 sourceBody580_144

def sourceBody580_146 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 6)

def sourceBody580_147 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody580_148 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody580_0, 580, 6)) (some 70) ([10]) (some (10, sourceBody580_147, 580, 7))

def sourceBody580_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_148 sourceBody580_3

def sourceBody580_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_149 sourceBody580_0

def sourceBody580_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_146 sourceBody580_150

def sourceBody580_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_0 sourceBody580_151

def sourceBody580_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_0 sourceBody580_152

def sourceBody580_154 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_145 sourceBody580_153

def sourceBody580_155 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody580_156 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody580_0, 580, 8)) (some 68) ([10]) (some (10, sourceBody580_147, 580, 9))

def sourceBody580_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_156 sourceBody580_3

def sourceBody580_158 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_157 sourceBody580_0

def sourceBody580_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_155 sourceBody580_158

def sourceBody580_160 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
        [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
          Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
            (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
      Flapjack.WordLangExpHOL.const 296#64])

def sourceBody580_161 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 4)

def sourceBody580_162 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 8)

def sourceBody580_163 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 10) 14

def sourceBody580_164 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_163 sourceBody580_0

def sourceBody580_165 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_162 sourceBody580_164

def sourceBody580_166 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_165 sourceBody580_0

def sourceBody580_167 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_161 sourceBody580_166

def sourceBody580_168 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_0 sourceBody580_167

def sourceBody580_169 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_160 sourceBody580_168

def sourceBody580_170 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_0 sourceBody580_169

def sourceBody580_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_159 sourceBody580_170

def sourceBody580_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_0 sourceBody580_171

def sourceBody580_173 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_0 sourceBody580_172

def sourceBody580_174 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_154 sourceBody580_173

def sourceBody580_175 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 12)

def sourceBody580_176 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 33#64)

def sourceBody580_177 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 296#64]))

def sourceBody580_178 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody580_0, 580, 10)) (some 158) ([10, 8, 14]) (some (10, sourceBody580_147, 580, 11))

def sourceBody580_179 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_178 sourceBody580_3

def sourceBody580_180 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_179 sourceBody580_0

def sourceBody580_181 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_177 sourceBody580_180

def sourceBody580_182 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_176 sourceBody580_181

def sourceBody580_183 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_175 sourceBody580_182

def sourceBody580_184 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_0 sourceBody580_183

def sourceBody580_185 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_0 sourceBody580_184

def sourceBody580_186 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_174 sourceBody580_185

def sourceBody580_187 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 24#64)

def sourceBody580_188 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody580_0, 580, 12)) (some 68) ([10]) (some (10, sourceBody580_147, 580, 13))

def sourceBody580_189 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_188 sourceBody580_3

def sourceBody580_190 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_189 sourceBody580_0

def sourceBody580_191 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_187 sourceBody580_190

def sourceBody580_192 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
        [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
          Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
            (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
      Flapjack.WordLangExpHOL.const 304#64])

def sourceBody580_193 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_192 sourceBody580_168

def sourceBody580_194 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_0 sourceBody580_193

def sourceBody580_195 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_191 sourceBody580_194

def sourceBody580_196 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_0 sourceBody580_195

def sourceBody580_197 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_0 sourceBody580_196

def sourceBody580_198 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_186 sourceBody580_197

def sourceBody580_199 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody580_200 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 20#64)

def sourceBody580_201 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody580_202 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody580_203 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.less) 8 (Flapjack.WordRegImm.reg 14) sourceBody580_201 sourceBody580_202

def sourceBody580_204 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_203 sourceBody580_3

def sourceBody580_205 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 8)

def sourceBody580_206 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 304#64]),
      Flapjack.WordLangExpHOL.var 4])

def sourceBody580_207 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 255#64)

def sourceBody580_208 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.store8 8 (Flapjack.WordLangAddr.addr 10 0#64))

def sourceBody580_209 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_208 sourceBody580_0

def sourceBody580_210 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_207 sourceBody580_209

def sourceBody580_211 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_206 sourceBody580_210

def sourceBody580_212 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody580_213 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 10)

def sourceBody580_214 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_213 sourceBody580_0

def sourceBody580_215 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_214 sourceBody580_0

def sourceBody580_216 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_212 sourceBody580_215

def sourceBody580_217 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_0 sourceBody580_216

def sourceBody580_218 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_211 sourceBody580_217

def sourceBody580_219 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody580_220 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_218 sourceBody580_219

def sourceBody580_221 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody580_222 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 2 (Flapjack.WordRegImm.imm 0#64) sourceBody580_220 sourceBody580_221

def sourceBody580_223 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_222 sourceBody580_3

def sourceBody580_224 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_223 sourceBody580_0

def sourceBody580_225 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_205 sourceBody580_224

def sourceBody580_226 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_204 sourceBody580_225

def sourceBody580_227 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_200 sourceBody580_226

def sourceBody580_228 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_161 sourceBody580_227

def sourceBody580_229 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
  PUnit.unit Flapjack.Spt.ln) sourceBody580_228 (Flapjack.Spt.ls PUnit.unit)

def sourceBody580_230 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_229 sourceBody580_3

def sourceBody580_231 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_3 sourceBody580_230

def sourceBody580_232 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 304#64]),
      Flapjack.WordLangExpHOL.const 19#64])

def sourceBody580_233 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 254#64)

def sourceBody580_234 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_233 sourceBody580_209

def sourceBody580_235 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_232 sourceBody580_234

def sourceBody580_236 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_231 sourceBody580_235

def sourceBody580_237 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 24#64)

def sourceBody580_238 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody580_239 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody580_0, 580, 14)) (some 68) ([8]) (some (8, sourceBody580_238, 580, 15))

def sourceBody580_240 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_239 sourceBody580_3

def sourceBody580_241 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_240 sourceBody580_0

def sourceBody580_242 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_237 sourceBody580_241

def sourceBody580_243 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
        [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
          Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
            (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
      Flapjack.WordLangExpHOL.const 312#64])

def sourceBody580_244 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 10)

def sourceBody580_245 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 14)

def sourceBody580_246 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 8) 2

def sourceBody580_247 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_246 sourceBody580_0

def sourceBody580_248 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_245 sourceBody580_247

def sourceBody580_249 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_248 sourceBody580_0

def sourceBody580_250 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_244 sourceBody580_249

def sourceBody580_251 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_0 sourceBody580_250

def sourceBody580_252 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_243 sourceBody580_251

def sourceBody580_253 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_0 sourceBody580_252

def sourceBody580_254 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_242 sourceBody580_253

def sourceBody580_255 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_0 sourceBody580_254

def sourceBody580_256 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_0 sourceBody580_255

def sourceBody580_257 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_236 sourceBody580_256

def sourceBody580_258 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 312#64]))

def sourceBody580_259 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 24#64)

def sourceBody580_260 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody580_0, 580, 16)) (some 78) ([8, 14]) (some (8, sourceBody580_238, 580, 17))

def sourceBody580_261 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_260 sourceBody580_3

def sourceBody580_262 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_261 sourceBody580_0

def sourceBody580_263 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_259 sourceBody580_262

def sourceBody580_264 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_258 sourceBody580_263

def sourceBody580_265 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_0 sourceBody580_264

def sourceBody580_266 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_0 sourceBody580_265

def sourceBody580_267 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_257 sourceBody580_266

def sourceBody580_268 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 8#64)

def sourceBody580_269 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody580_0, 580, 18)) (some 68) ([8]) (some (8, sourceBody580_238, 580, 19))

def sourceBody580_270 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_269 sourceBody580_3

def sourceBody580_271 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_270 sourceBody580_0

def sourceBody580_272 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_268 sourceBody580_271

def sourceBody580_273 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
        [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
          Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
            (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
      Flapjack.WordLangExpHOL.const 264#64])

def sourceBody580_274 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_273 sourceBody580_251

def sourceBody580_275 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_0 sourceBody580_274

def sourceBody580_276 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_272 sourceBody580_275

def sourceBody580_277 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_0 sourceBody580_276

def sourceBody580_278 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_0 sourceBody580_277

def sourceBody580_279 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_267 sourceBody580_278

def sourceBody580_280 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
              (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
        Flapjack.WordLangExpHOL.const 264#64]))

def sourceBody580_281 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 8#64)

def sourceBody580_282 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody580_0, 580, 20)) (some 78) ([8, 14]) (some (8, sourceBody580_238, 580, 21))

def sourceBody580_283 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_282 sourceBody580_3

def sourceBody580_284 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_283 sourceBody580_0

def sourceBody580_285 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_281 sourceBody580_284

def sourceBody580_286 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_280 sourceBody580_285

def sourceBody580_287 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_0 sourceBody580_286

def sourceBody580_288 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_0 sourceBody580_287

def sourceBody580_289 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_279 sourceBody580_288

def sourceBody580_290 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody580_291 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody580_0, 580, 22)) (some 68) ([8]) (some (8, sourceBody580_238, 580, 23))

def sourceBody580_292 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_291 sourceBody580_3

def sourceBody580_293 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_292 sourceBody580_0

def sourceBody580_294 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_290 sourceBody580_293

def sourceBody580_295 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
        [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
          Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
            (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
      Flapjack.WordLangExpHOL.const 280#64])

def sourceBody580_296 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_295 sourceBody580_251

def sourceBody580_297 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_0 sourceBody580_296

def sourceBody580_298 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_294 sourceBody580_297

def sourceBody580_299 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_0 sourceBody580_298

def sourceBody580_300 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_0 sourceBody580_299

def sourceBody580_301 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_289 sourceBody580_300

def sourceBody580_302 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 96#64)

def sourceBody580_303 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody580_0, 580, 24)) (some 68) ([8]) (some (8, sourceBody580_238, 580, 25))

def sourceBody580_304 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_303 sourceBody580_3

def sourceBody580_305 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_304 sourceBody580_0

def sourceBody580_306 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_302 sourceBody580_305

def sourceBody580_307 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
        [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
          Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
            (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
      Flapjack.WordLangExpHOL.const 272#64])

def sourceBody580_308 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_307 sourceBody580_251

def sourceBody580_309 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_0 sourceBody580_308

def sourceBody580_310 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_306 sourceBody580_309

def sourceBody580_311 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_0 sourceBody580_310

def sourceBody580_312 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_0 sourceBody580_311

def sourceBody580_313 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_301 sourceBody580_312

def sourceBody580_314 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody580_315 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [10]

def sourceBody580_316 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_315 sourceBody580_0

def sourceBody580_317 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_314 sourceBody580_316

def sourceBody580_318 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_313 sourceBody580_317

def sourceBody580_319 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_199 sourceBody580_318

def sourceBody580_320 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_0 sourceBody580_319

def sourceBody580_321 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_198 sourceBody580_320

def sourceBody580_322 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_11 sourceBody580_321

def sourceBody580_323 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_0 sourceBody580_322

def sourceBody580_324 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_0 sourceBody580_323

def sourceBody580_325 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_5 sourceBody580_324

def sourceBody580_326 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_0 sourceBody580_325

def sourceBody580_327 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody580_0 sourceBody580_326

def source580 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (580, 1, sourceBody580_327)
end InitECandidate.Proofs.WordStages
