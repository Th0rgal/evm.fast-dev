import InitECandidate.Proofs.WordStages.Source809
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody825_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody825_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 2)

def sourceBody825_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 18#64)

def sourceBody825_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 26

def sourceBody825_4 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln, Flapjack.Spt.ln)), sourceBody825_0, 825, 2)) (some 80) ([26, 6]) (some (26, sourceBody825_3, 825, 3))

def sourceBody825_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody825_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody825_4 sourceBody825_5

def sourceBody825_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody825_6 sourceBody825_0

def sourceBody825_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody825_2 sourceBody825_7

def sourceBody825_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody825_1 sourceBody825_8

def sourceBody825_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 10)

def sourceBody825_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody825_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody825_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody825_14 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 6 (Flapjack.WordRegImm.reg 24) sourceBody825_12 sourceBody825_13

def sourceBody825_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody825_14 sourceBody825_5

def sourceBody825_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 6)

def sourceBody825_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody825_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [26]

def sourceBody825_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody825_18 sourceBody825_0

def sourceBody825_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody825_17 sourceBody825_19

def sourceBody825_21 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 16 (Flapjack.WordRegImm.imm 0#64) sourceBody825_20 sourceBody825_0

def sourceBody825_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody825_21 sourceBody825_5

def sourceBody825_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody825_22 sourceBody825_0

def sourceBody825_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody825_16 sourceBody825_23

def sourceBody825_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody825_15 sourceBody825_24

def sourceBody825_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody825_11 sourceBody825_25

def sourceBody825_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody825_10 sourceBody825_26

def sourceBody825_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 18#64])

def sourceBody825_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 26 (Flapjack.WordLangAddr.addr 26 0#64))

def sourceBody825_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody825_29 sourceBody825_0

def sourceBody825_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody825_28 sourceBody825_30

def sourceBody825_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 26)

def sourceBody825_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 19#64])

def sourceBody825_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 24 (Flapjack.WordLangAddr.addr 24 0#64))

def sourceBody825_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody825_34 sourceBody825_0

def sourceBody825_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody825_33 sourceBody825_35

def sourceBody825_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 24)

def sourceBody825_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 6)

def sourceBody825_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody825_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody825_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody825_42 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 4 (Flapjack.WordRegImm.reg 22) sourceBody825_40 sourceBody825_41

def sourceBody825_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody825_42 sourceBody825_5

def sourceBody825_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 4)

def sourceBody825_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 16)

def sourceBody825_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody825_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.const 18#64)

def sourceBody825_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [32]

def sourceBody825_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody825_48 sourceBody825_0

def sourceBody825_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody825_47 sourceBody825_49

def sourceBody825_51 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.WordRegImm.imm 0#64) sourceBody825_50 sourceBody825_0

def sourceBody825_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody825_51 sourceBody825_5

def sourceBody825_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody825_52 sourceBody825_0

def sourceBody825_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody825_44 sourceBody825_53

def sourceBody825_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody825_43 sourceBody825_54

def sourceBody825_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody825_46 sourceBody825_55

def sourceBody825_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody825_45 sourceBody825_56

def sourceBody825_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody825_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody825_58 sourceBody825_49

def sourceBody825_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody825_57 sourceBody825_59

def sourceBody825_61 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.WordRegImm.imm 0#64) sourceBody825_60 sourceBody825_0

def sourceBody825_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody825_61 sourceBody825_5

def sourceBody825_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody825_62 sourceBody825_0

def sourceBody825_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody825_44 sourceBody825_63

def sourceBody825_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody825_43 sourceBody825_64

def sourceBody825_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody825_39 sourceBody825_65

def sourceBody825_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody825_38 sourceBody825_66

def sourceBody825_68 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 4 (Flapjack.WordRegImm.reg 22) sourceBody825_40 sourceBody825_41

def sourceBody825_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody825_68 sourceBody825_5

def sourceBody825_70 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.WordRegImm.imm 0#64) sourceBody825_59 sourceBody825_0

def sourceBody825_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody825_70 sourceBody825_5

def sourceBody825_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody825_71 sourceBody825_0

def sourceBody825_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody825_44 sourceBody825_72

def sourceBody825_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody825_69 sourceBody825_73

def sourceBody825_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody825_46 sourceBody825_74

def sourceBody825_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody825_38 sourceBody825_75

def sourceBody825_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody825_67 sourceBody825_76

def sourceBody825_78 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notLower) 4 (Flapjack.WordRegImm.reg 22) sourceBody825_40 sourceBody825_41

def sourceBody825_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody825_78 sourceBody825_5

def sourceBody825_80 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody825_81 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 4)

def sourceBody825_82 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody825_83 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 30 (Flapjack.WordRegImm.reg 8) sourceBody825_82 sourceBody825_80

def sourceBody825_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody825_83 sourceBody825_5

def sourceBody825_85 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 17#64)

def sourceBody825_86 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 16)

def sourceBody825_87 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody825_88 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody825_89 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notLower) 18 (Flapjack.WordRegImm.reg 34) sourceBody825_87 sourceBody825_88

def sourceBody825_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody825_89 sourceBody825_5

def sourceBody825_91 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody825_92 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 18)

def sourceBody825_93 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody825_94 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 20 (Flapjack.WordRegImm.reg 12) sourceBody825_93 sourceBody825_91

def sourceBody825_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody825_94 sourceBody825_5

def sourceBody825_96 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and [Flapjack.WordLangExpHOL.var 30, Flapjack.WordLangExpHOL.var 20])

def sourceBody825_97 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 16)

def sourceBody825_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody825_97 sourceBody825_49

def sourceBody825_99 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 28 (Flapjack.WordRegImm.imm 0#64) sourceBody825_98 sourceBody825_0

def sourceBody825_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody825_99 sourceBody825_5

def sourceBody825_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody825_100 sourceBody825_0

def sourceBody825_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody825_96 sourceBody825_101

def sourceBody825_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody825_95 sourceBody825_102

def sourceBody825_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody825_92 sourceBody825_103

def sourceBody825_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody825_91 sourceBody825_104

def sourceBody825_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody825_90 sourceBody825_105

def sourceBody825_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody825_86 sourceBody825_106

def sourceBody825_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody825_85 sourceBody825_107

def sourceBody825_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody825_84 sourceBody825_108

def sourceBody825_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody825_81 sourceBody825_109

def sourceBody825_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody825_80 sourceBody825_110

def sourceBody825_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody825_79 sourceBody825_111

def sourceBody825_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody825_39 sourceBody825_112

def sourceBody825_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody825_45 sourceBody825_113

def sourceBody825_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody825_77 sourceBody825_114

def sourceBody825_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody825_115 sourceBody825_59

def sourceBody825_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody825_37 sourceBody825_116

def sourceBody825_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody825_36 sourceBody825_117

def sourceBody825_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody825_32 sourceBody825_118

def sourceBody825_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody825_31 sourceBody825_119

def sourceBody825_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody825_27 sourceBody825_120

def sourceBody825_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody825_9 sourceBody825_121

def sourceBody825_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody825_0 sourceBody825_122

def sourceBody825_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody825_0 sourceBody825_123

def source825 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (825, 2, sourceBody825_124)
end InitECandidate.Proofs.WordStages
