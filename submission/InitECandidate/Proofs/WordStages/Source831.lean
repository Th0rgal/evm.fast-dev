import InitECandidate.Proofs.WordStages.Source815
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody831_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody831_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 2)

def sourceBody831_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 4)

def sourceBody831_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 32

def sourceBody831_4 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody831_0, 831, 2)) (some 93) ([32, 26]) (some (32, sourceBody831_3, 831, 3))

def sourceBody831_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody831_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody831_4 sourceBody831_5

def sourceBody831_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody831_6 sourceBody831_0

def sourceBody831_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody831_2 sourceBody831_7

def sourceBody831_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody831_1 sourceBody831_8

def sourceBody831_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32
  (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 7#64])
    (Flapjack.WordLangExpHOL.const 3#64))

def sourceBody831_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 16#64)

def sourceBody831_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody831_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 18)

def sourceBody831_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody831_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody831_16 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 22 (Flapjack.WordRegImm.reg 34) sourceBody831_14 sourceBody831_15

def sourceBody831_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody831_16 sourceBody831_5

def sourceBody831_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 22)

def sourceBody831_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38
  (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 32)
    (Flapjack.WordLangExpHOL.const 1#64))

def sourceBody831_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 32)

def sourceBody831_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.longMul 34 34 38 22))

def sourceBody831_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 34)

def sourceBody831_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody831_22 sourceBody831_0

def sourceBody831_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody831_21 sourceBody831_23

def sourceBody831_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody831_20 sourceBody831_24

def sourceBody831_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody831_19 sourceBody831_25

def sourceBody831_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody831_26 sourceBody831_0

def sourceBody831_28 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 28 (Flapjack.WordRegImm.imm 0#64) sourceBody831_27 sourceBody831_0

def sourceBody831_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody831_28 sourceBody831_5

def sourceBody831_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody831_29 sourceBody831_0

def sourceBody831_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody831_18 sourceBody831_30

def sourceBody831_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody831_17 sourceBody831_31

def sourceBody831_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody831_13 sourceBody831_32

def sourceBody831_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody831_12 sourceBody831_33

def sourceBody831_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 8)

def sourceBody831_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 10)

def sourceBody831_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 12)

def sourceBody831_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 14)

def sourceBody831_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 22

def sourceBody831_40 : WordLangProgHOL (BitVec 64) :=
.call (some (([38]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody831_0, 831, 4)) (some 138) ([22, 34, 28, 40]) (some (22, sourceBody831_39, 831, 5))

def sourceBody831_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody831_40 sourceBody831_5

def sourceBody831_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody831_41 sourceBody831_0

def sourceBody831_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody831_38 sourceBody831_42

def sourceBody831_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody831_37 sourceBody831_43

def sourceBody831_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody831_36 sourceBody831_44

def sourceBody831_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody831_35 sourceBody831_45

def sourceBody831_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody831_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 38)

def sourceBody831_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody831_50 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 34 (Flapjack.WordRegImm.reg 28) sourceBody831_49 sourceBody831_47

def sourceBody831_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody831_50 sourceBody831_5

def sourceBody831_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 34)

def sourceBody831_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 38, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody831_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 22)

def sourceBody831_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody831_54 sourceBody831_0

def sourceBody831_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody831_55 sourceBody831_0

def sourceBody831_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody831_53 sourceBody831_56

def sourceBody831_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody831_0 sourceBody831_57

def sourceBody831_59 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 40 (Flapjack.WordRegImm.imm 0#64) sourceBody831_58 sourceBody831_0

def sourceBody831_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody831_59 sourceBody831_5

def sourceBody831_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody831_60 sourceBody831_0

def sourceBody831_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody831_52 sourceBody831_61

def sourceBody831_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody831_51 sourceBody831_62

def sourceBody831_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody831_48 sourceBody831_63

def sourceBody831_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody831_47 sourceBody831_64

def sourceBody831_66 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody831_67 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 6)

def sourceBody831_68 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody831_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody831_70 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notLower) 28 (Flapjack.WordRegImm.reg 40) sourceBody831_68 sourceBody831_69

def sourceBody831_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody831_70 sourceBody831_5

def sourceBody831_72 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 28)

def sourceBody831_73 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 38)

def sourceBody831_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody831_73 sourceBody831_0

def sourceBody831_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody831_74 sourceBody831_0

def sourceBody831_76 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 32#64])
        (Flapjack.WordLangExpHOL.const 4#64),
      Flapjack.WordLangExpHOL.var 38])

def sourceBody831_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody831_76 sourceBody831_0

def sourceBody831_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody831_77 sourceBody831_0

def sourceBody831_79 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 16 (Flapjack.WordRegImm.imm 0#64) sourceBody831_75 sourceBody831_78

def sourceBody831_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody831_79 sourceBody831_5

def sourceBody831_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody831_80 sourceBody831_0

def sourceBody831_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody831_72 sourceBody831_81

def sourceBody831_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody831_71 sourceBody831_82

def sourceBody831_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody831_67 sourceBody831_83

def sourceBody831_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody831_66 sourceBody831_84

def sourceBody831_86 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody831_87 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 28 (Flapjack.WordRegImm.reg 40) sourceBody831_68 sourceBody831_69

def sourceBody831_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody831_87 sourceBody831_5

def sourceBody831_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody831_14 sourceBody831_0

def sourceBody831_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody831_89 sourceBody831_0

def sourceBody831_91 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 16 (Flapjack.WordRegImm.imm 0#64) sourceBody831_90 sourceBody831_0

def sourceBody831_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody831_91 sourceBody831_5

def sourceBody831_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody831_92 sourceBody831_0

def sourceBody831_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody831_72 sourceBody831_93

def sourceBody831_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody831_88 sourceBody831_94

def sourceBody831_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody831_86 sourceBody831_95

def sourceBody831_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody831_18 sourceBody831_96

def sourceBody831_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody831_85 sourceBody831_97

def sourceBody831_99 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 26)

def sourceBody831_100 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.longMul 40 40 34 28))

def sourceBody831_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody831_100 sourceBody831_0

def sourceBody831_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody831_18 sourceBody831_101

def sourceBody831_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody831_99 sourceBody831_102

def sourceBody831_104 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 40)

def sourceBody831_105 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 16)

def sourceBody831_106 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.const 500#64)

def sourceBody831_107 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody831_108 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody831_109 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 24 (Flapjack.WordRegImm.reg 36) sourceBody831_107 sourceBody831_108

def sourceBody831_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody831_109 sourceBody831_5

def sourceBody831_111 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 24)

def sourceBody831_112 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 500#64)

def sourceBody831_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody831_112 sourceBody831_0

def sourceBody831_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody831_113 sourceBody831_0

def sourceBody831_115 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 20 (Flapjack.WordRegImm.imm 0#64) sourceBody831_114 sourceBody831_0

def sourceBody831_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody831_115 sourceBody831_5

def sourceBody831_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody831_116 sourceBody831_0

def sourceBody831_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody831_111 sourceBody831_117

def sourceBody831_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody831_110 sourceBody831_118

def sourceBody831_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody831_106 sourceBody831_119

def sourceBody831_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody831_105 sourceBody831_120

def sourceBody831_122 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 16)

def sourceBody831_123 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [30]

def sourceBody831_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody831_123 sourceBody831_0

def sourceBody831_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody831_122 sourceBody831_124

def sourceBody831_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody831_121 sourceBody831_125

def sourceBody831_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody831_104 sourceBody831_126

def sourceBody831_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody831_103 sourceBody831_127

def sourceBody831_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody831_98 sourceBody831_128

def sourceBody831_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody831_0 sourceBody831_129

def sourceBody831_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody831_0 sourceBody831_130

def sourceBody831_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody831_65 sourceBody831_131

def sourceBody831_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody831_46 sourceBody831_132

def sourceBody831_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody831_0 sourceBody831_133

def sourceBody831_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody831_0 sourceBody831_134

def sourceBody831_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody831_34 sourceBody831_135

def sourceBody831_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody831_11 sourceBody831_136

def sourceBody831_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody831_0 sourceBody831_137

def sourceBody831_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody831_10 sourceBody831_138

def sourceBody831_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody831_0 sourceBody831_139

def sourceBody831_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody831_9 sourceBody831_140

def sourceBody831_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody831_0 sourceBody831_141

def sourceBody831_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody831_0 sourceBody831_142

def source831 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (831, 8, sourceBody831_143)
end InitECandidate.Proofs.WordStages
