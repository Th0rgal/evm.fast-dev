import InitECandidate.Proofs.WordStages.Source436
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody452_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 6)

def sourceBody452_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody452_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody452_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody452_4 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 20 (Flapjack.WordRegImm.reg 16) sourceBody452_2 sourceBody452_3

def sourceBody452_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody452_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody452_4 sourceBody452_5

def sourceBody452_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 20)

def sourceBody452_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.load (Flapjack.WordLangExpHOL.var 4))

def sourceBody452_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.load (Flapjack.WordLangExpHOL.var 2))

def sourceBody452_10 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 20 (Flapjack.WordRegImm.reg 16) sourceBody452_2 sourceBody452_3

def sourceBody452_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody452_10 sourceBody452_5

def sourceBody452_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody452_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [10]

def sourceBody452_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody452_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody452_13 sourceBody452_14

def sourceBody452_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody452_12 sourceBody452_15

def sourceBody452_17 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 26 (Flapjack.WordRegImm.imm 0#64) sourceBody452_16 sourceBody452_14

def sourceBody452_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody452_17 sourceBody452_5

def sourceBody452_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody452_18 sourceBody452_14

def sourceBody452_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody452_7 sourceBody452_19

def sourceBody452_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody452_11 sourceBody452_20

def sourceBody452_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody452_9 sourceBody452_21

def sourceBody452_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody452_8 sourceBody452_22

def sourceBody452_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody452_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody452_24 sourceBody452_15

def sourceBody452_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody452_23 sourceBody452_25

def sourceBody452_27 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 26 (Flapjack.WordRegImm.imm 0#64) sourceBody452_26 sourceBody452_14

def sourceBody452_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody452_27 sourceBody452_5

def sourceBody452_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody452_28 sourceBody452_14

def sourceBody452_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody452_7 sourceBody452_29

def sourceBody452_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody452_6 sourceBody452_30

def sourceBody452_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody452_1 sourceBody452_31

def sourceBody452_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody452_0 sourceBody452_32

def sourceBody452_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 20#64)

def sourceBody452_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 6)

def sourceBody452_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 2#64)

def sourceBody452_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody452_38 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 16 (Flapjack.WordRegImm.reg 26) sourceBody452_37 sourceBody452_1

def sourceBody452_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody452_38 sourceBody452_5

def sourceBody452_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 16)

def sourceBody452_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody452_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody452_41 sourceBody452_14

def sourceBody452_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody452_42 sourceBody452_14

def sourceBody452_44 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.WordRegImm.imm 0#64) sourceBody452_43 sourceBody452_14

def sourceBody452_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody452_44 sourceBody452_5

def sourceBody452_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody452_45 sourceBody452_14

def sourceBody452_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody452_40 sourceBody452_46

def sourceBody452_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody452_39 sourceBody452_47

def sourceBody452_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody452_36 sourceBody452_48

def sourceBody452_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody452_35 sourceBody452_49

def sourceBody452_51 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 10)

def sourceBody452_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody452_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody452_54 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.less) 26 (Flapjack.WordRegImm.reg 8) sourceBody452_52 sourceBody452_53

def sourceBody452_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody452_54 sourceBody452_5

def sourceBody452_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 26)

def sourceBody452_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.var 20])

def sourceBody452_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 16 (Flapjack.WordLangAddr.addr 16 0#64))

def sourceBody452_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody452_58 sourceBody452_14

def sourceBody452_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody452_57 sourceBody452_59

def sourceBody452_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 16)

def sourceBody452_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.var 20])

def sourceBody452_63 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 8 (Flapjack.WordLangAddr.addr 8 0#64))

def sourceBody452_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody452_63 sourceBody452_14

def sourceBody452_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody452_62 sourceBody452_64

def sourceBody452_66 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 8)

def sourceBody452_67 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 26)

def sourceBody452_68 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 18)

def sourceBody452_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody452_70 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody452_71 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 24 (Flapjack.WordRegImm.reg 12) sourceBody452_69 sourceBody452_70

def sourceBody452_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody452_71 sourceBody452_5

def sourceBody452_73 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 24)

def sourceBody452_74 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 18)

def sourceBody452_75 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 26)

def sourceBody452_76 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 24 (Flapjack.WordRegImm.reg 12) sourceBody452_69 sourceBody452_70

def sourceBody452_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody452_76 sourceBody452_5

def sourceBody452_78 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody452_79 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [14]

def sourceBody452_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody452_79 sourceBody452_14

def sourceBody452_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody452_78 sourceBody452_80

def sourceBody452_82 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 22 (Flapjack.WordRegImm.imm 0#64) sourceBody452_81 sourceBody452_14

def sourceBody452_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody452_82 sourceBody452_5

def sourceBody452_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody452_83 sourceBody452_14

def sourceBody452_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody452_73 sourceBody452_84

def sourceBody452_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody452_77 sourceBody452_85

def sourceBody452_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody452_75 sourceBody452_86

def sourceBody452_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody452_74 sourceBody452_87

def sourceBody452_89 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody452_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody452_89 sourceBody452_80

def sourceBody452_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody452_88 sourceBody452_90

def sourceBody452_92 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 22 (Flapjack.WordRegImm.imm 0#64) sourceBody452_91 sourceBody452_14

def sourceBody452_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody452_92 sourceBody452_5

def sourceBody452_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody452_93 sourceBody452_14

def sourceBody452_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody452_73 sourceBody452_94

def sourceBody452_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody452_72 sourceBody452_95

def sourceBody452_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody452_68 sourceBody452_96

def sourceBody452_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody452_67 sourceBody452_97

def sourceBody452_99 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 20, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody452_100 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 14)

def sourceBody452_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody452_100 sourceBody452_14

def sourceBody452_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody452_101 sourceBody452_14

def sourceBody452_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody452_99 sourceBody452_102

def sourceBody452_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody452_14 sourceBody452_103

def sourceBody452_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody452_98 sourceBody452_104

def sourceBody452_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody452_66 sourceBody452_105

def sourceBody452_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody452_65 sourceBody452_106

def sourceBody452_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody452_61 sourceBody452_107

def sourceBody452_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody452_60 sourceBody452_108

def sourceBody452_110 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody452_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody452_109 sourceBody452_110

def sourceBody452_112 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody452_113 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 18 (Flapjack.WordRegImm.imm 0#64) sourceBody452_111 sourceBody452_112

def sourceBody452_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody452_113 sourceBody452_5

def sourceBody452_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody452_114 sourceBody452_14

def sourceBody452_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody452_56 sourceBody452_115

def sourceBody452_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody452_55 sourceBody452_116

def sourceBody452_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody452_51 sourceBody452_117

def sourceBody452_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody452_7 sourceBody452_118

def sourceBody452_120 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln))
  PUnit.unit Flapjack.Spt.ln) sourceBody452_119 (Flapjack.Spt.ls PUnit.unit)

def sourceBody452_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody452_120 sourceBody452_5

def sourceBody452_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody452_5 sourceBody452_121

def sourceBody452_123 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [16]

def sourceBody452_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody452_123 sourceBody452_14

def sourceBody452_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody452_1 sourceBody452_124

def sourceBody452_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody452_122 sourceBody452_125

def sourceBody452_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody452_3 sourceBody452_126

def sourceBody452_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody452_14 sourceBody452_127

def sourceBody452_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody452_50 sourceBody452_128

def sourceBody452_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody452_34 sourceBody452_129

def sourceBody452_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody452_14 sourceBody452_130

def sourceBody452_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody452_33 sourceBody452_131

def source452 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (452, 4, sourceBody452_132)
end InitECandidate.Proofs.WordStages
