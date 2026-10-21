import InitECandidate.Proofs.WordStages.Source293
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody309_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody309_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 32#64]))

def sourceBody309_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 40#64]))

def sourceBody309_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 32)

def sourceBody309_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 6)

def sourceBody309_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody309_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody309_7 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 26 (Flapjack.WordRegImm.reg 18) sourceBody309_5 sourceBody309_6

def sourceBody309_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody309_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody309_7 sourceBody309_8

def sourceBody309_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 26)

def sourceBody309_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 20)

def sourceBody309_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 4)

def sourceBody309_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 32)

def sourceBody309_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 26

def sourceBody309_15 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody309_0, 309, 2)) (some 79) ([26, 18, 30]) (some (26, sourceBody309_14, 309, 3))

def sourceBody309_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody309_15 sourceBody309_8

def sourceBody309_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody309_16 sourceBody309_0

def sourceBody309_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody309_13 sourceBody309_17

def sourceBody309_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody309_12 sourceBody309_18

def sourceBody309_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody309_11 sourceBody309_19

def sourceBody309_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 14)

def sourceBody309_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody309_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody309_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody309_25 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 18 (Flapjack.WordRegImm.reg 30) sourceBody309_23 sourceBody309_24

def sourceBody309_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody309_25 sourceBody309_8

def sourceBody309_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 18)

def sourceBody309_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 48#64])

def sourceBody309_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 8)

def sourceBody309_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 18)

def sourceBody309_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 26) 30

def sourceBody309_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody309_31 sourceBody309_0

def sourceBody309_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody309_30 sourceBody309_32

def sourceBody309_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody309_33 sourceBody309_0

def sourceBody309_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody309_29 sourceBody309_34

def sourceBody309_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody309_0 sourceBody309_35

def sourceBody309_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody309_28 sourceBody309_36

def sourceBody309_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody309_0 sourceBody309_37

def sourceBody309_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 56#64])

def sourceBody309_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 10)

def sourceBody309_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody309_40 sourceBody309_34

def sourceBody309_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody309_0 sourceBody309_41

def sourceBody309_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody309_39 sourceBody309_42

def sourceBody309_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody309_0 sourceBody309_43

def sourceBody309_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody309_38 sourceBody309_44

def sourceBody309_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 2)

def sourceBody309_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [26]

def sourceBody309_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody309_47 sourceBody309_0

def sourceBody309_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody309_46 sourceBody309_48

def sourceBody309_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody309_45 sourceBody309_49

def sourceBody309_51 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 16 (Flapjack.WordRegImm.imm 0#64) sourceBody309_50 sourceBody309_0

def sourceBody309_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody309_51 sourceBody309_8

def sourceBody309_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody309_52 sourceBody309_0

def sourceBody309_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody309_27 sourceBody309_53

def sourceBody309_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody309_26 sourceBody309_54

def sourceBody309_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody309_22 sourceBody309_55

def sourceBody309_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody309_21 sourceBody309_56

def sourceBody309_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody309_20 sourceBody309_57

def sourceBody309_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody309_0 sourceBody309_58

def sourceBody309_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody309_0 sourceBody309_59

def sourceBody309_61 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 30 (Flapjack.WordRegImm.imm 0#64) sourceBody309_60 sourceBody309_0

def sourceBody309_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody309_61 sourceBody309_8

def sourceBody309_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody309_62 sourceBody309_0

def sourceBody309_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody309_10 sourceBody309_63

def sourceBody309_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody309_9 sourceBody309_64

def sourceBody309_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody309_4 sourceBody309_65

def sourceBody309_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody309_3 sourceBody309_66

def sourceBody309_68 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 32)

def sourceBody309_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 4)

def sourceBody309_70 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 6)

def sourceBody309_71 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody309_0, 309, 4)) (some 287) ([26, 18, 30, 16]) (some (26, sourceBody309_14, 309, 5))

def sourceBody309_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody309_71 sourceBody309_8

def sourceBody309_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody309_72 sourceBody309_0

def sourceBody309_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody309_70 sourceBody309_73

def sourceBody309_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody309_69 sourceBody309_74

def sourceBody309_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody309_68 sourceBody309_75

def sourceBody309_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody309_11 sourceBody309_76

def sourceBody309_78 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 20, Flapjack.WordLangExpHOL.var 14])

def sourceBody309_79 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 32, Flapjack.WordLangExpHOL.var 14])

def sourceBody309_80 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 48#64]))

def sourceBody309_81 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 56#64]))

def sourceBody309_82 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.var 14])

def sourceBody309_83 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.var 14])

def sourceBody309_84 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 8)

def sourceBody309_85 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 10)

def sourceBody309_86 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody309_87 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody309_0, 309, 6)) (some 308) ([18, 30, 16, 28, 22, 34, 12, 24]) (some (18, sourceBody309_86, 309, 7))

def sourceBody309_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody309_87 sourceBody309_8

def sourceBody309_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody309_88 sourceBody309_0

def sourceBody309_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody309_85 sourceBody309_89

def sourceBody309_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody309_84 sourceBody309_90

def sourceBody309_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody309_83 sourceBody309_91

def sourceBody309_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody309_82 sourceBody309_92

def sourceBody309_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody309_81 sourceBody309_93

def sourceBody309_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody309_80 sourceBody309_94

def sourceBody309_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody309_79 sourceBody309_95

def sourceBody309_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody309_78 sourceBody309_96

def sourceBody309_98 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 14)

def sourceBody309_99 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody309_100 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 30 (Flapjack.WordRegImm.reg 16) sourceBody309_99 sourceBody309_22

def sourceBody309_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody309_100 sourceBody309_8

def sourceBody309_102 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 30)

def sourceBody309_103 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 20)

def sourceBody309_104 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 14)

def sourceBody309_105 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 26)

def sourceBody309_106 : WordLangProgHOL (BitVec 64) :=
.call (none) (some 293) ([0, 18, 30, 16]) (none)

def sourceBody309_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody309_106 sourceBody309_0

def sourceBody309_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody309_105 sourceBody309_107

def sourceBody309_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody309_104 sourceBody309_108

def sourceBody309_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody309_103 sourceBody309_109

def sourceBody309_111 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 28 (Flapjack.WordRegImm.imm 0#64) sourceBody309_110 sourceBody309_0

def sourceBody309_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody309_111 sourceBody309_8

def sourceBody309_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody309_112 sourceBody309_0

def sourceBody309_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody309_102 sourceBody309_113

def sourceBody309_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody309_101 sourceBody309_114

def sourceBody309_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody309_98 sourceBody309_115

def sourceBody309_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody309_22 sourceBody309_116

def sourceBody309_118 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 26)

def sourceBody309_119 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [18]

def sourceBody309_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody309_119 sourceBody309_0

def sourceBody309_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody309_118 sourceBody309_120

def sourceBody309_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody309_117 sourceBody309_121

def sourceBody309_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody309_97 sourceBody309_122

def sourceBody309_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody309_0 sourceBody309_123

def sourceBody309_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody309_0 sourceBody309_124

def sourceBody309_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody309_77 sourceBody309_125

def sourceBody309_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody309_0 sourceBody309_126

def sourceBody309_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody309_0 sourceBody309_127

def sourceBody309_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody309_67 sourceBody309_128

def sourceBody309_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody309_2 sourceBody309_129

def sourceBody309_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody309_0 sourceBody309_130

def sourceBody309_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody309_1 sourceBody309_131

def sourceBody309_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody309_0 sourceBody309_132

def source309 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (309, 6, sourceBody309_133)
end InitECandidate.Proofs.WordStages
