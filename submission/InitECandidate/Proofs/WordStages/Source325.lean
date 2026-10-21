import InitECandidate.Proofs.WordStages.Source309
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody325_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 2)

def sourceBody325_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody325_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody325_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody325_4 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 8 (Flapjack.WordRegImm.reg 14) sourceBody325_2 sourceBody325_3

def sourceBody325_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody325_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_4 sourceBody325_5

def sourceBody325_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 8)

def sourceBody325_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 4)

def sourceBody325_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 128#64)

def sourceBody325_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.store8 8 (Flapjack.WordLangAddr.addr 16 0#64))

def sourceBody325_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody325_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_10 sourceBody325_11

def sourceBody325_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_9 sourceBody325_12

def sourceBody325_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_8 sourceBody325_13

def sourceBody325_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody325_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [16]

def sourceBody325_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_16 sourceBody325_11

def sourceBody325_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_15 sourceBody325_17

def sourceBody325_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_14 sourceBody325_18

def sourceBody325_20 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.imm 0#64) sourceBody325_19 sourceBody325_11

def sourceBody325_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_20 sourceBody325_5

def sourceBody325_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_21 sourceBody325_11

def sourceBody325_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_7 sourceBody325_22

def sourceBody325_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_6 sourceBody325_23

def sourceBody325_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_1 sourceBody325_24

def sourceBody325_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_0 sourceBody325_25

def sourceBody325_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 0#64]))

def sourceBody325_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 160#64)

def sourceBody325_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_28 sourceBody325_12

def sourceBody325_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_8 sourceBody325_29

def sourceBody325_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody325_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody325_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody325_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody325_35 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody325_11, 325, 2)) (some 77) ([8, 14, 10]) (some (8, sourceBody325_34, 325, 3))

def sourceBody325_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_35 sourceBody325_5

def sourceBody325_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_36 sourceBody325_11

def sourceBody325_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_33 sourceBody325_37

def sourceBody325_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_32 sourceBody325_38

def sourceBody325_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_31 sourceBody325_39

def sourceBody325_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_11 sourceBody325_40

def sourceBody325_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_11 sourceBody325_41

def sourceBody325_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_30 sourceBody325_42

def sourceBody325_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 33#64)

def sourceBody325_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_44 sourceBody325_17

def sourceBody325_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_43 sourceBody325_45

def sourceBody325_47 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.imm 0#64) sourceBody325_46 sourceBody325_11

def sourceBody325_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_47 sourceBody325_5

def sourceBody325_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_48 sourceBody325_11

def sourceBody325_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_7 sourceBody325_49

def sourceBody325_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_6 sourceBody325_50

def sourceBody325_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_1 sourceBody325_51

def sourceBody325_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_27 sourceBody325_52

def sourceBody325_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_26 sourceBody325_53

def sourceBody325_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody325_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 13#64)

def sourceBody325_57 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody325_11, 325, 4)) (some 282) ([8]) (some (8, sourceBody325_34, 325, 5))

def sourceBody325_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_57 sourceBody325_5

def sourceBody325_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_58 sourceBody325_11

def sourceBody325_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_56 sourceBody325_59

def sourceBody325_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_11 sourceBody325_60

def sourceBody325_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_11 sourceBody325_61

def sourceBody325_63 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.imm 0#64) sourceBody325_62 sourceBody325_11

def sourceBody325_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_63 sourceBody325_5

def sourceBody325_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_64 sourceBody325_11

def sourceBody325_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_7 sourceBody325_65

def sourceBody325_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_6 sourceBody325_66

def sourceBody325_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_1 sourceBody325_67

def sourceBody325_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_55 sourceBody325_68

def sourceBody325_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_54 sourceBody325_69

def sourceBody325_71 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody325_72 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody325_73 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody325_74 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody325_75 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody325_76 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 10 (Flapjack.WordRegImm.reg 18) sourceBody325_74 sourceBody325_75

def sourceBody325_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_76 sourceBody325_5

def sourceBody325_78 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 10)

def sourceBody325_79 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 4)

def sourceBody325_80 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 16)

def sourceBody325_81 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 8)

def sourceBody325_82 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody325_83 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody325_11, 325, 6)) (some 77) ([10, 18, 6]) (some (10, sourceBody325_82, 325, 7))

def sourceBody325_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_83 sourceBody325_5

def sourceBody325_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_84 sourceBody325_11

def sourceBody325_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_81 sourceBody325_85

def sourceBody325_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_80 sourceBody325_86

def sourceBody325_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_79 sourceBody325_87

def sourceBody325_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_11 sourceBody325_88

def sourceBody325_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_11 sourceBody325_89

def sourceBody325_91 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 8)

def sourceBody325_92 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [14]

def sourceBody325_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_92 sourceBody325_11

def sourceBody325_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_91 sourceBody325_93

def sourceBody325_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_90 sourceBody325_94

def sourceBody325_96 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.WordRegImm.imm 0#64) sourceBody325_95 sourceBody325_11

def sourceBody325_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_96 sourceBody325_5

def sourceBody325_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_97 sourceBody325_11

def sourceBody325_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_78 sourceBody325_98

def sourceBody325_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_77 sourceBody325_99

def sourceBody325_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_73 sourceBody325_100

def sourceBody325_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_7 sourceBody325_101

def sourceBody325_103 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 2)

def sourceBody325_104 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody325_11, 325, 8)) (some 324) ([10]) (some (10, sourceBody325_82, 325, 9))

def sourceBody325_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_104 sourceBody325_5

def sourceBody325_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_105 sourceBody325_11

def sourceBody325_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_103 sourceBody325_106

def sourceBody325_108 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 160#64)

def sourceBody325_109 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.store8 18 (Flapjack.WordLangAddr.addr 10 0#64))

def sourceBody325_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_109 sourceBody325_11

def sourceBody325_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_108 sourceBody325_110

def sourceBody325_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_79 sourceBody325_111

def sourceBody325_113 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody325_114 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 14)

def sourceBody325_115 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody325_116 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody325_117 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody325_11, 325, 10)) (some 77) ([18, 6, 12]) (some (18, sourceBody325_116, 325, 11))

def sourceBody325_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_117 sourceBody325_5

def sourceBody325_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_118 sourceBody325_11

def sourceBody325_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_115 sourceBody325_119

def sourceBody325_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_114 sourceBody325_120

def sourceBody325_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_113 sourceBody325_121

def sourceBody325_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_11 sourceBody325_122

def sourceBody325_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_11 sourceBody325_123

def sourceBody325_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_112 sourceBody325_124

def sourceBody325_126 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 33#64)

def sourceBody325_127 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [10]

def sourceBody325_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_127 sourceBody325_11

def sourceBody325_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_126 sourceBody325_128

def sourceBody325_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_125 sourceBody325_129

def sourceBody325_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_107 sourceBody325_130

def sourceBody325_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_11 sourceBody325_131

def sourceBody325_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_11 sourceBody325_132

def sourceBody325_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_102 sourceBody325_133

def sourceBody325_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_72 sourceBody325_134

def sourceBody325_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_11 sourceBody325_135

def sourceBody325_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_71 sourceBody325_136

def sourceBody325_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_11 sourceBody325_137

def sourceBody325_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody325_70 sourceBody325_138

def source325 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (325, 3, sourceBody325_139)
end InitECandidate.Proofs.WordStages
