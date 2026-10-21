import InitECandidate.Proofs.WordStages.Source365
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody381_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody381_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 2)

def sourceBody381_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 4)

def sourceBody381_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody381_4 : WordLangProgHOL (BitVec 64) :=
.call (some (([24, 8, 20]), ((Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln, Flapjack.Spt.ln)), sourceBody381_0, 381, 2)) (some 380) ([14, 28]) (some (14, sourceBody381_3, 381, 3))

def sourceBody381_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody381_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_4 sourceBody381_5

def sourceBody381_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_6 sourceBody381_0

def sourceBody381_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_2 sourceBody381_7

def sourceBody381_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_1 sourceBody381_8

def sourceBody381_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 144#64]))

def sourceBody381_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 4294967295#64)

def sourceBody381_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 14)

def sourceBody381_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody381_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody381_15 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 6 (Flapjack.WordRegImm.reg 18) sourceBody381_13 sourceBody381_14

def sourceBody381_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_15 sourceBody381_5

def sourceBody381_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 6)

def sourceBody381_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 66#64)

def sourceBody381_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 28)

def sourceBody381_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_19 sourceBody381_0

def sourceBody381_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_20 sourceBody381_0

def sourceBody381_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_18 sourceBody381_21

def sourceBody381_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_0 sourceBody381_22

def sourceBody381_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 6#64)

def sourceBody381_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 28

def sourceBody381_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_24 sourceBody381_25

def sourceBody381_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_23 sourceBody381_26

def sourceBody381_28 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.imm 0#64) sourceBody381_27 sourceBody381_0

def sourceBody381_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_28 sourceBody381_5

def sourceBody381_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_29 sourceBody381_0

def sourceBody381_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_17 sourceBody381_30

def sourceBody381_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_16 sourceBody381_31

def sourceBody381_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_12 sourceBody381_32

def sourceBody381_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_11 sourceBody381_33

def sourceBody381_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 14)

def sourceBody381_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 24, Flapjack.WordLangExpHOL.var 8])

def sourceBody381_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 60#64)

def sourceBody381_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_37 sourceBody381_21

def sourceBody381_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_0 sourceBody381_38

def sourceBody381_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_39 sourceBody381_26

def sourceBody381_41 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.imm 0#64) sourceBody381_40 sourceBody381_0

def sourceBody381_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_41 sourceBody381_5

def sourceBody381_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_42 sourceBody381_0

def sourceBody381_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_17 sourceBody381_43

def sourceBody381_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_16 sourceBody381_44

def sourceBody381_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_36 sourceBody381_45

def sourceBody381_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_35 sourceBody381_46

def sourceBody381_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_34 sourceBody381_47

def sourceBody381_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 20)

def sourceBody381_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 61#64)

def sourceBody381_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_50 sourceBody381_21

def sourceBody381_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_0 sourceBody381_51

def sourceBody381_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_52 sourceBody381_26

def sourceBody381_54 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.imm 0#64) sourceBody381_53 sourceBody381_0

def sourceBody381_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_54 sourceBody381_5

def sourceBody381_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_55 sourceBody381_0

def sourceBody381_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_17 sourceBody381_56

def sourceBody381_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_16 sourceBody381_57

def sourceBody381_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_49 sourceBody381_58

def sourceBody381_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_35 sourceBody381_59

def sourceBody381_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_48 sourceBody381_60

def sourceBody381_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 152#64]))

def sourceBody381_63 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody381_64 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 6 (Flapjack.WordRegImm.reg 18) sourceBody381_13 sourceBody381_14

def sourceBody381_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_64 sourceBody381_5

def sourceBody381_66 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 131072#64)

def sourceBody381_67 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 200#64]))

def sourceBody381_68 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 62#64)

def sourceBody381_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_68 sourceBody381_21

def sourceBody381_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_0 sourceBody381_69

def sourceBody381_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_70 sourceBody381_26

def sourceBody381_72 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.imm 0#64) sourceBody381_71 sourceBody381_0

def sourceBody381_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_72 sourceBody381_5

def sourceBody381_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_73 sourceBody381_0

def sourceBody381_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_17 sourceBody381_74

def sourceBody381_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_16 sourceBody381_75

def sourceBody381_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_67 sourceBody381_76

def sourceBody381_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_66 sourceBody381_77

def sourceBody381_79 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.imm 0#64) sourceBody381_78 sourceBody381_0

def sourceBody381_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_79 sourceBody381_5

def sourceBody381_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_80 sourceBody381_0

def sourceBody381_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_17 sourceBody381_81

def sourceBody381_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_65 sourceBody381_82

def sourceBody381_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_63 sourceBody381_83

def sourceBody381_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_62 sourceBody381_84

def sourceBody381_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_61 sourceBody381_85

def sourceBody381_87 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 16777216#64)

def sourceBody381_88 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 24)

def sourceBody381_89 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 63#64)

def sourceBody381_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_89 sourceBody381_21

def sourceBody381_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_0 sourceBody381_90

def sourceBody381_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_91 sourceBody381_26

def sourceBody381_93 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.imm 0#64) sourceBody381_92 sourceBody381_0

def sourceBody381_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_93 sourceBody381_5

def sourceBody381_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_94 sourceBody381_0

def sourceBody381_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_17 sourceBody381_95

def sourceBody381_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_16 sourceBody381_96

def sourceBody381_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_88 sourceBody381_97

def sourceBody381_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_87 sourceBody381_98

def sourceBody381_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_86 sourceBody381_99

def sourceBody381_101 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 64#64)

def sourceBody381_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_101 sourceBody381_21

def sourceBody381_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_0 sourceBody381_102

def sourceBody381_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_103 sourceBody381_26

def sourceBody381_105 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.imm 0#64) sourceBody381_104 sourceBody381_0

def sourceBody381_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_105 sourceBody381_5

def sourceBody381_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_106 sourceBody381_0

def sourceBody381_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_17 sourceBody381_107

def sourceBody381_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_16 sourceBody381_108

def sourceBody381_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_49 sourceBody381_109

def sourceBody381_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_87 sourceBody381_110

def sourceBody381_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_100 sourceBody381_111

def sourceBody381_113 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody381_114 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 16#64],
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody381_115 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 16#64],
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody381_116 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 16#64],
        Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody381_117 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 28)

def sourceBody381_118 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 6)

def sourceBody381_119 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 18)

def sourceBody381_120 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 12)

def sourceBody381_121 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody381_122 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody381_0, 381, 4)) (some 101) ([10, 22, 16, 30]) (some (10, sourceBody381_121, 381, 5))

def sourceBody381_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_122 sourceBody381_5

def sourceBody381_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_123 sourceBody381_0

def sourceBody381_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_120 sourceBody381_124

def sourceBody381_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_119 sourceBody381_125

def sourceBody381_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_118 sourceBody381_126

def sourceBody381_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_117 sourceBody381_127

def sourceBody381_129 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 26)

def sourceBody381_130 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody381_131 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody381_132 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody381_133 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 22 (Flapjack.WordRegImm.reg 16) sourceBody381_131 sourceBody381_132

def sourceBody381_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_133 sourceBody381_5

def sourceBody381_135 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 22)

def sourceBody381_136 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 65#64)

def sourceBody381_137 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 10)

def sourceBody381_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_137 sourceBody381_0

def sourceBody381_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_138 sourceBody381_0

def sourceBody381_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_136 sourceBody381_139

def sourceBody381_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_0 sourceBody381_140

def sourceBody381_142 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 6#64)

def sourceBody381_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_142 sourceBody381_121

def sourceBody381_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_141 sourceBody381_143

def sourceBody381_145 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 30 (Flapjack.WordRegImm.imm 0#64) sourceBody381_144 sourceBody381_0

def sourceBody381_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_145 sourceBody381_5

def sourceBody381_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_146 sourceBody381_0

def sourceBody381_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_135 sourceBody381_147

def sourceBody381_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_134 sourceBody381_148

def sourceBody381_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_130 sourceBody381_149

def sourceBody381_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_129 sourceBody381_150

def sourceBody381_152 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 28)

def sourceBody381_153 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.const 0#64, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody381_154 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_153 sourceBody381_149

def sourceBody381_155 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_152 sourceBody381_154

def sourceBody381_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_151 sourceBody381_155

def sourceBody381_157 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 24)

def sourceBody381_158 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 8)

def sourceBody381_159 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 20)

def sourceBody381_160 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [10, 22, 16]

def sourceBody381_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_160 sourceBody381_0

def sourceBody381_162 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_159 sourceBody381_161

def sourceBody381_163 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_158 sourceBody381_162

def sourceBody381_164 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_157 sourceBody381_163

def sourceBody381_165 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_156 sourceBody381_164

def sourceBody381_166 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_128 sourceBody381_165

def sourceBody381_167 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_0 sourceBody381_166

def sourceBody381_168 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_0 sourceBody381_167

def sourceBody381_169 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_116 sourceBody381_168

def sourceBody381_170 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_0 sourceBody381_169

def sourceBody381_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_115 sourceBody381_170

def sourceBody381_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_0 sourceBody381_171

def sourceBody381_173 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_114 sourceBody381_172

def sourceBody381_174 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_0 sourceBody381_173

def sourceBody381_175 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_113 sourceBody381_174

def sourceBody381_176 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_0 sourceBody381_175

def sourceBody381_177 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_112 sourceBody381_176

def sourceBody381_178 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_10 sourceBody381_177

def sourceBody381_179 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_0 sourceBody381_178

def sourceBody381_180 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_9 sourceBody381_179

def sourceBody381_181 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_0 sourceBody381_180

def sourceBody381_182 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_0 sourceBody381_181

def sourceBody381_183 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_0 sourceBody381_182

def sourceBody381_184 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_0 sourceBody381_183

def sourceBody381_185 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_0 sourceBody381_184

def sourceBody381_186 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody381_0 sourceBody381_185

def source381 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (381, 3, sourceBody381_186)
end InitECandidate.Proofs.WordStages
