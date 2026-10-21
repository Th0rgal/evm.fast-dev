import InitECandidate.Proofs.WordStages.Source325
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody341_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 4)

def sourceBody341_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody341_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody341_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody341_4 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 12 (Flapjack.WordRegImm.reg 38) sourceBody341_2 sourceBody341_3

def sourceBody341_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody341_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_4 sourceBody341_5

def sourceBody341_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 12)

def sourceBody341_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody341_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody341_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 46)

def sourceBody341_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_10 sourceBody341_8

def sourceBody341_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_11 sourceBody341_8

def sourceBody341_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_9 sourceBody341_12

def sourceBody341_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_13

def sourceBody341_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.const 6#64)

def sourceBody341_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 46

def sourceBody341_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_15 sourceBody341_16

def sourceBody341_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_14 sourceBody341_17

def sourceBody341_19 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 26 (Flapjack.WordRegImm.imm 0#64) sourceBody341_18 sourceBody341_8

def sourceBody341_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_19 sourceBody341_5

def sourceBody341_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_20 sourceBody341_8

def sourceBody341_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_7 sourceBody341_21

def sourceBody341_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_6 sourceBody341_22

def sourceBody341_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_1 sourceBody341_23

def sourceBody341_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_0 sourceBody341_24

def sourceBody341_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 2)

def sourceBody341_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 46 (Flapjack.WordLangAddr.addr 46 0#64))

def sourceBody341_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_27 sourceBody341_8

def sourceBody341_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_26 sourceBody341_28

def sourceBody341_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 46)

def sourceBody341_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 400#64)

def sourceBody341_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 26

def sourceBody341_33 : WordLangProgHOL (BitVec 64) :=
.call (some (([38]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody341_8, 341, 2)) (some 68) ([26]) (some (26, sourceBody341_32, 341, 3))

def sourceBody341_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_33 sourceBody341_5

def sourceBody341_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_34 sourceBody341_8

def sourceBody341_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_31 sourceBody341_35

def sourceBody341_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 38)

def sourceBody341_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 400#64)

def sourceBody341_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 54

def sourceBody341_40 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        Flapjack.Spt.ln)
      PUnit.unit (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody341_8, 341, 4)) (some 78) ([54, 8]) (some (54, sourceBody341_39, 341, 5))

def sourceBody341_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_40 sourceBody341_5

def sourceBody341_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_41 sourceBody341_8

def sourceBody341_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_38 sourceBody341_42

def sourceBody341_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_37 sourceBody341_43

def sourceBody341_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_44

def sourceBody341_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_45

def sourceBody341_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 38, Flapjack.WordLangExpHOL.const 384#64])

def sourceBody341_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 2)

def sourceBody341_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 54)

def sourceBody341_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 26) 8

def sourceBody341_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_50 sourceBody341_8

def sourceBody341_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_49 sourceBody341_51

def sourceBody341_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_52 sourceBody341_8

def sourceBody341_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_48 sourceBody341_53

def sourceBody341_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_54

def sourceBody341_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_47 sourceBody341_55

def sourceBody341_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_56

def sourceBody341_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_46 sourceBody341_57

def sourceBody341_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 38, Flapjack.WordLangExpHOL.const 392#64])

def sourceBody341_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 4)

def sourceBody341_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_60 sourceBody341_53

def sourceBody341_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_61

def sourceBody341_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_59 sourceBody341_62

def sourceBody341_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_63

def sourceBody341_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_58 sourceBody341_64

def sourceBody341_66 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody341_67 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.const 9#64)

def sourceBody341_68 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 12)

def sourceBody341_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody341_70 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody341_71 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody341_72 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notLower) 42 (Flapjack.WordRegImm.reg 30) sourceBody341_70 sourceBody341_71

def sourceBody341_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_72 sourceBody341_5

def sourceBody341_74 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody341_75 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 42)

def sourceBody341_76 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody341_77 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.WordRegImm.reg 32) sourceBody341_76 sourceBody341_74

def sourceBody341_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_77 sourceBody341_5

def sourceBody341_79 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.const 4#64)

def sourceBody341_80 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 12)

def sourceBody341_81 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody341_82 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody341_83 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notLower) 48 (Flapjack.WordRegImm.reg 14) sourceBody341_81 sourceBody341_82

def sourceBody341_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_83 sourceBody341_5

def sourceBody341_85 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody341_86 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.var 48)

def sourceBody341_87 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody341_88 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 28 (Flapjack.WordRegImm.reg 56) sourceBody341_87 sourceBody341_85

def sourceBody341_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_88 sourceBody341_5

def sourceBody341_90 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.var 28])

def sourceBody341_91 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody341_92 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody341_93 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody341_94 : WordLangProgHOL (BitVec 64) :=
.call (some (([26, 54, 8, 34]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody341_8, 341, 6)) (some 162) ([16, 42]) (some (16, sourceBody341_93, 341, 7))

def sourceBody341_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_94 sourceBody341_5

def sourceBody341_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_95 sourceBody341_8

def sourceBody341_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_92 sourceBody341_96

def sourceBody341_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_91 sourceBody341_97

def sourceBody341_99 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 12)

def sourceBody341_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_99 sourceBody341_8

def sourceBody341_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_100 sourceBody341_8

def sourceBody341_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_98 sourceBody341_101

def sourceBody341_103 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 22)

def sourceBody341_104 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 42 (Flapjack.WordRegImm.reg 30) sourceBody341_70 sourceBody341_71

def sourceBody341_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_104 sourceBody341_5

def sourceBody341_106 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.var 42)

def sourceBody341_107 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.const 11#64)

def sourceBody341_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_107 sourceBody341_8

def sourceBody341_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_108 sourceBody341_8

def sourceBody341_110 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 58 (Flapjack.WordRegImm.imm 0#64) sourceBody341_109 sourceBody341_8

def sourceBody341_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_110 sourceBody341_5

def sourceBody341_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_111 sourceBody341_8

def sourceBody341_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_106 sourceBody341_112

def sourceBody341_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_105 sourceBody341_113

def sourceBody341_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_69 sourceBody341_114

def sourceBody341_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_103 sourceBody341_115

def sourceBody341_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_102 sourceBody341_116

def sourceBody341_118 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 2#64)

def sourceBody341_119 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.const 12#64)

def sourceBody341_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_119 sourceBody341_8

def sourceBody341_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_120 sourceBody341_8

def sourceBody341_122 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 58 (Flapjack.WordRegImm.imm 0#64) sourceBody341_121 sourceBody341_8

def sourceBody341_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_122 sourceBody341_5

def sourceBody341_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_123 sourceBody341_8

def sourceBody341_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_106 sourceBody341_124

def sourceBody341_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_105 sourceBody341_125

def sourceBody341_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_118 sourceBody341_126

def sourceBody341_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_103 sourceBody341_127

def sourceBody341_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_117 sourceBody341_128

def sourceBody341_130 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 3#64)

def sourceBody341_131 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.const 14#64)

def sourceBody341_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_131 sourceBody341_8

def sourceBody341_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_132 sourceBody341_8

def sourceBody341_134 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 58 (Flapjack.WordRegImm.imm 0#64) sourceBody341_133 sourceBody341_8

def sourceBody341_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_134 sourceBody341_5

def sourceBody341_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_135 sourceBody341_8

def sourceBody341_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_106 sourceBody341_136

def sourceBody341_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_105 sourceBody341_137

def sourceBody341_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_130 sourceBody341_138

def sourceBody341_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_103 sourceBody341_139

def sourceBody341_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_129 sourceBody341_140

def sourceBody341_142 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 4#64)

def sourceBody341_143 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.const 13#64)

def sourceBody341_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_143 sourceBody341_8

def sourceBody341_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_144 sourceBody341_8

def sourceBody341_146 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 58 (Flapjack.WordRegImm.imm 0#64) sourceBody341_145 sourceBody341_8

def sourceBody341_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_146 sourceBody341_5

def sourceBody341_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_147 sourceBody341_8

def sourceBody341_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_106 sourceBody341_148

def sourceBody341_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_105 sourceBody341_149

def sourceBody341_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_142 sourceBody341_150

def sourceBody341_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_103 sourceBody341_151

def sourceBody341_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_141 sourceBody341_152

def sourceBody341_154 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 192#64)

def sourceBody341_155 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.const 254#64)

def sourceBody341_156 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 2)

def sourceBody341_157 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 4)

def sourceBody341_158 : WordLangProgHOL (BitVec 64) :=
.call (some (([26, 54, 8, 34]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody341_8, 341, 8)) (some 162) ([16, 42]) (some (16, sourceBody341_93, 341, 9))

def sourceBody341_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_158 sourceBody341_5

def sourceBody341_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_159 sourceBody341_8

def sourceBody341_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_157 sourceBody341_160

def sourceBody341_162 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_156 sourceBody341_161

def sourceBody341_163 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 2#64)

def sourceBody341_164 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 16)

def sourceBody341_165 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_164 sourceBody341_8

def sourceBody341_166 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_165 sourceBody341_8

def sourceBody341_167 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_163 sourceBody341_166

def sourceBody341_168 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_167

def sourceBody341_169 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 6#64)

def sourceBody341_170 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_169 sourceBody341_93

def sourceBody341_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_168 sourceBody341_170

def sourceBody341_172 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.imm 0#64) sourceBody341_162 sourceBody341_171

def sourceBody341_173 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_172 sourceBody341_5

def sourceBody341_174 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_173 sourceBody341_8

def sourceBody341_175 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_90 sourceBody341_174

def sourceBody341_176 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_89 sourceBody341_175

def sourceBody341_177 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_86 sourceBody341_176

def sourceBody341_178 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_85 sourceBody341_177

def sourceBody341_179 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_84 sourceBody341_178

def sourceBody341_180 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_80 sourceBody341_179

def sourceBody341_181 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_155 sourceBody341_180

def sourceBody341_182 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_78 sourceBody341_181

def sourceBody341_183 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_75 sourceBody341_182

def sourceBody341_184 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_74 sourceBody341_183

def sourceBody341_185 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_73 sourceBody341_184

def sourceBody341_186 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_154 sourceBody341_185

def sourceBody341_187 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_68 sourceBody341_186

def sourceBody341_188 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.imm 0#64) sourceBody341_153 sourceBody341_187

def sourceBody341_189 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_188 sourceBody341_5

def sourceBody341_190 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_189 sourceBody341_8

def sourceBody341_191 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_90 sourceBody341_190

def sourceBody341_192 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_89 sourceBody341_191

def sourceBody341_193 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_86 sourceBody341_192

def sourceBody341_194 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_85 sourceBody341_193

def sourceBody341_195 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_84 sourceBody341_194

def sourceBody341_196 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_80 sourceBody341_195

def sourceBody341_197 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_79 sourceBody341_196

def sourceBody341_198 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_78 sourceBody341_197

def sourceBody341_199 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_75 sourceBody341_198

def sourceBody341_200 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_74 sourceBody341_199

def sourceBody341_201 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_73 sourceBody341_200

def sourceBody341_202 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_69 sourceBody341_201

def sourceBody341_203 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_68 sourceBody341_202

def sourceBody341_204 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 38, Flapjack.WordLangExpHOL.const 0#64])

def sourceBody341_205 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 42)

def sourceBody341_206 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 16) 30

def sourceBody341_207 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_206 sourceBody341_8

def sourceBody341_208 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_205 sourceBody341_207

def sourceBody341_209 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_208 sourceBody341_8

def sourceBody341_210 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_103 sourceBody341_209

def sourceBody341_211 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_210

def sourceBody341_212 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_204 sourceBody341_211

def sourceBody341_213 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_212

def sourceBody341_214 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_203 sourceBody341_213

def sourceBody341_215 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 26)

def sourceBody341_216 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 42 (Flapjack.WordRegImm.reg 30) sourceBody341_70 sourceBody341_71

def sourceBody341_217 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_216 sourceBody341_5

def sourceBody341_218 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 3#64)

def sourceBody341_219 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_218 sourceBody341_166

def sourceBody341_220 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_219

def sourceBody341_221 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_220 sourceBody341_170

def sourceBody341_222 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 58 (Flapjack.WordRegImm.imm 0#64) sourceBody341_221 sourceBody341_8

def sourceBody341_223 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_222 sourceBody341_5

def sourceBody341_224 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_223 sourceBody341_8

def sourceBody341_225 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_106 sourceBody341_224

def sourceBody341_226 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_217 sourceBody341_225

def sourceBody341_227 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_69 sourceBody341_226

def sourceBody341_228 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_215 sourceBody341_227

def sourceBody341_229 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_214 sourceBody341_228

def sourceBody341_230 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 54)

def sourceBody341_231 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.var 8)

def sourceBody341_232 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 30

def sourceBody341_233 : WordLangProgHOL (BitVec 64) :=
.call (some (([16, 42]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody341_8, 341, 10)) (some 169) ([30, 58]) (some (30, sourceBody341_232, 341, 11))

def sourceBody341_234 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_233 sourceBody341_5

def sourceBody341_235 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_234 sourceBody341_8

def sourceBody341_236 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_231 sourceBody341_235

def sourceBody341_237 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_230 sourceBody341_236

def sourceBody341_238 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 16)

def sourceBody341_239 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 42)

def sourceBody341_240 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 50)

def sourceBody341_241 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 6)

def sourceBody341_242 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.const 4#64)

def sourceBody341_243 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 58)

def sourceBody341_244 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_243 sourceBody341_8

def sourceBody341_245 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_244 sourceBody341_8

def sourceBody341_246 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_242 sourceBody341_245

def sourceBody341_247 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_246

def sourceBody341_248 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.const 6#64)

def sourceBody341_249 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 58

def sourceBody341_250 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_248 sourceBody341_249

def sourceBody341_251 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_247 sourceBody341_250

def sourceBody341_252 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 20 (Flapjack.WordRegImm.imm 0#64) sourceBody341_251 sourceBody341_8

def sourceBody341_253 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_252 sourceBody341_5

def sourceBody341_254 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_253 sourceBody341_8

def sourceBody341_255 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_241 sourceBody341_254

def sourceBody341_256 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_78 sourceBody341_255

def sourceBody341_257 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_240 sourceBody341_256

def sourceBody341_258 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_239 sourceBody341_257

def sourceBody341_259 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody341_260 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 22)

def sourceBody341_261 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody341_262 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody341_263 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 20 (Flapjack.WordRegImm.reg 48) sourceBody341_261 sourceBody341_262

def sourceBody341_264 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_263 sourceBody341_5

def sourceBody341_265 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 20)

def sourceBody341_266 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 30)

def sourceBody341_267 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.const 8#64)

def sourceBody341_268 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 12#64)

def sourceBody341_269 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 32

def sourceBody341_270 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        Flapjack.Spt.ln)
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody341_8, 341, 12)) (some 333) ([32, 20, 48, 14]) (some (32, sourceBody341_269, 341, 13))

def sourceBody341_271 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_270 sourceBody341_5

def sourceBody341_272 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_271 sourceBody341_8

def sourceBody341_273 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_268 sourceBody341_272

def sourceBody341_274 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_267 sourceBody341_273

def sourceBody341_275 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_262 sourceBody341_274

def sourceBody341_276 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_266 sourceBody341_275

def sourceBody341_277 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 38, Flapjack.WordLangExpHOL.const 8#64])

def sourceBody341_278 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 20)

def sourceBody341_279 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 32) 48

def sourceBody341_280 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_279 sourceBody341_8

def sourceBody341_281 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_278 sourceBody341_280

def sourceBody341_282 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_281 sourceBody341_8

def sourceBody341_283 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_241 sourceBody341_282

def sourceBody341_284 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_283

def sourceBody341_285 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_277 sourceBody341_284

def sourceBody341_286 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_285

def sourceBody341_287 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_276 sourceBody341_286

def sourceBody341_288 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody341_289 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_288 sourceBody341_8

def sourceBody341_290 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_289 sourceBody341_8

def sourceBody341_291 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_287 sourceBody341_290

def sourceBody341_292 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.WordRegImm.imm 0#64) sourceBody341_291 sourceBody341_8

def sourceBody341_293 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_292 sourceBody341_5

def sourceBody341_294 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_293 sourceBody341_8

def sourceBody341_295 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_265 sourceBody341_294

def sourceBody341_296 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_264 sourceBody341_295

def sourceBody341_297 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_82 sourceBody341_296

def sourceBody341_298 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_260 sourceBody341_297

def sourceBody341_299 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 22)

def sourceBody341_300 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.const 4#64)

def sourceBody341_301 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 28 (Flapjack.WordRegImm.reg 56) sourceBody341_87 sourceBody341_85

def sourceBody341_302 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_301 sourceBody341_5

def sourceBody341_303 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 28)

def sourceBody341_304 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 30)

def sourceBody341_305 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 58)

def sourceBody341_306 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.const 8#64)

def sourceBody341_307 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 12#64)

def sourceBody341_308 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 40

def sourceBody341_309 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody341_8, 341, 14)) (some 333) ([40, 28, 56, 10]) (some (40, sourceBody341_308, 341, 15))

def sourceBody341_310 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_309 sourceBody341_5

def sourceBody341_311 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_310 sourceBody341_8

def sourceBody341_312 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_307 sourceBody341_311

def sourceBody341_313 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_306 sourceBody341_312

def sourceBody341_314 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_305 sourceBody341_313

def sourceBody341_315 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_304 sourceBody341_314

def sourceBody341_316 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 6)

def sourceBody341_317 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_316 sourceBody341_8

def sourceBody341_318 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_262 sourceBody341_8

def sourceBody341_319 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_82 sourceBody341_8

def sourceBody341_320 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody341_321 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_320 sourceBody341_8

def sourceBody341_322 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_321 sourceBody341_8

def sourceBody341_323 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_319 sourceBody341_322

def sourceBody341_324 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_318 sourceBody341_323

def sourceBody341_325 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_317 sourceBody341_324

def sourceBody341_326 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_315 sourceBody341_325

def sourceBody341_327 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody341_328 : WordLangProgHOL (BitVec 64) :=
.call (some (([32, 20, 48, 14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody341_8, 341, 16)) (some 332) ([40, 28, 56]) (some (40, sourceBody341_308, 341, 17))

def sourceBody341_329 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_328 sourceBody341_5

def sourceBody341_330 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_329 sourceBody341_8

def sourceBody341_331 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_327 sourceBody341_330

def sourceBody341_332 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_305 sourceBody341_331

def sourceBody341_333 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_304 sourceBody341_332

def sourceBody341_334 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.imm 0#64) sourceBody341_326 sourceBody341_333

def sourceBody341_335 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_334 sourceBody341_5

def sourceBody341_336 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_335 sourceBody341_8

def sourceBody341_337 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_303 sourceBody341_336

def sourceBody341_338 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_302 sourceBody341_337

def sourceBody341_339 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_300 sourceBody341_338

def sourceBody341_340 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_299 sourceBody341_339

def sourceBody341_341 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 38, Flapjack.WordLangExpHOL.const 16#64])

def sourceBody341_342 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 32)

def sourceBody341_343 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.var 20)

def sourceBody341_344 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 48)

def sourceBody341_345 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 14)

def sourceBody341_346 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 28)

def sourceBody341_347 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 40) 24

def sourceBody341_348 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_347 sourceBody341_8

def sourceBody341_349 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_346 sourceBody341_348

def sourceBody341_350 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 56)

def sourceBody341_351 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 40, Flapjack.WordLangExpHOL.const 8#64])
  24

def sourceBody341_352 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_351 sourceBody341_8

def sourceBody341_353 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_350 sourceBody341_352

def sourceBody341_354 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 10)

def sourceBody341_355 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 40, Flapjack.WordLangExpHOL.const 16#64])
  24

def sourceBody341_356 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_355 sourceBody341_8

def sourceBody341_357 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_354 sourceBody341_356

def sourceBody341_358 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 36)

def sourceBody341_359 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 40, Flapjack.WordLangExpHOL.const 24#64])
  24

def sourceBody341_360 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_359 sourceBody341_8

def sourceBody341_361 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_358 sourceBody341_360

def sourceBody341_362 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_361 sourceBody341_8

def sourceBody341_363 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_357 sourceBody341_362

def sourceBody341_364 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_353 sourceBody341_363

def sourceBody341_365 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_349 sourceBody341_364

def sourceBody341_366 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_345 sourceBody341_365

def sourceBody341_367 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_366

def sourceBody341_368 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_344 sourceBody341_367

def sourceBody341_369 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_368

def sourceBody341_370 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_343 sourceBody341_369

def sourceBody341_371 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_370

def sourceBody341_372 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_342 sourceBody341_371

def sourceBody341_373 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_372

def sourceBody341_374 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_341 sourceBody341_373

def sourceBody341_375 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_374

def sourceBody341_376 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_340 sourceBody341_375

def sourceBody341_377 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 58, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody341_378 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.var 40)

def sourceBody341_379 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_378 sourceBody341_8

def sourceBody341_380 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_379 sourceBody341_8

def sourceBody341_381 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_377 sourceBody341_380

def sourceBody341_382 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_381

def sourceBody341_383 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_376 sourceBody341_382

def sourceBody341_384 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.var 22)

def sourceBody341_385 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notLower) 28 (Flapjack.WordRegImm.reg 56) sourceBody341_87 sourceBody341_85

def sourceBody341_386 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_385 sourceBody341_5

def sourceBody341_387 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody341_388 : WordLangProgHOL (BitVec 64) :=
.call (some (([32, 20, 48, 14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody341_8, 341, 18)) (some 332) ([40, 28, 56]) (some (40, sourceBody341_308, 341, 19))

def sourceBody341_389 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_388 sourceBody341_5

def sourceBody341_390 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_389 sourceBody341_8

def sourceBody341_391 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_387 sourceBody341_390

def sourceBody341_392 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_305 sourceBody341_391

def sourceBody341_393 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_304 sourceBody341_392

def sourceBody341_394 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 38, Flapjack.WordLangExpHOL.const 48#64])

def sourceBody341_395 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_394 sourceBody341_373

def sourceBody341_396 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_395

def sourceBody341_397 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_393 sourceBody341_396

def sourceBody341_398 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_397 sourceBody341_382

def sourceBody341_399 : WordLangProgHOL (BitVec 64) :=
.call (some (([32, 20, 48, 14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody341_8, 341, 20)) (some 332) ([40, 28, 56]) (some (40, sourceBody341_308, 341, 21))

def sourceBody341_400 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_399 sourceBody341_5

def sourceBody341_401 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_400 sourceBody341_8

def sourceBody341_402 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_387 sourceBody341_401

def sourceBody341_403 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_305 sourceBody341_402

def sourceBody341_404 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_304 sourceBody341_403

def sourceBody341_405 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 38, Flapjack.WordLangExpHOL.const 80#64])

def sourceBody341_406 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_405 sourceBody341_373

def sourceBody341_407 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_406

def sourceBody341_408 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_404 sourceBody341_407

def sourceBody341_409 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 58, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody341_410 : WordLangProgHOL (BitVec 64) :=
.call (some (([32, 20, 48, 14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody341_8, 341, 22)) (some 332) ([40, 28, 56]) (some (40, sourceBody341_308, 341, 23))

def sourceBody341_411 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_410 sourceBody341_5

def sourceBody341_412 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_411 sourceBody341_8

def sourceBody341_413 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_387 sourceBody341_412

def sourceBody341_414 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_409 sourceBody341_413

def sourceBody341_415 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_304 sourceBody341_414

def sourceBody341_416 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_408 sourceBody341_415

def sourceBody341_417 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 38, Flapjack.WordLangExpHOL.const 112#64])

def sourceBody341_418 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_417 sourceBody341_373

def sourceBody341_419 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_418

def sourceBody341_420 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_416 sourceBody341_419

def sourceBody341_421 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 58, Flapjack.WordLangExpHOL.const 2#64])

def sourceBody341_422 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_421 sourceBody341_380

def sourceBody341_423 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_422

def sourceBody341_424 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_420 sourceBody341_423

def sourceBody341_425 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.imm 0#64) sourceBody341_398 sourceBody341_424

def sourceBody341_426 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_425 sourceBody341_5

def sourceBody341_427 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_426 sourceBody341_8

def sourceBody341_428 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_303 sourceBody341_427

def sourceBody341_429 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_386 sourceBody341_428

def sourceBody341_430 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_384 sourceBody341_429

def sourceBody341_431 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_87 sourceBody341_430

def sourceBody341_432 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_383 sourceBody341_431

def sourceBody341_433 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 14#64)

def sourceBody341_434 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody341_8, 341, 24)) (some 333) ([40, 28, 56, 10]) (some (40, sourceBody341_308, 341, 25))

def sourceBody341_435 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_434 sourceBody341_5

def sourceBody341_436 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_435 sourceBody341_8

def sourceBody341_437 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_433 sourceBody341_436

def sourceBody341_438 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_387 sourceBody341_437

def sourceBody341_439 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_305 sourceBody341_438

def sourceBody341_440 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_304 sourceBody341_439

def sourceBody341_441 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_432 sourceBody341_440

def sourceBody341_442 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 38, Flapjack.WordLangExpHOL.const 144#64])

def sourceBody341_443 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 6)

def sourceBody341_444 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.var 28)

def sourceBody341_445 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 40) 56

def sourceBody341_446 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_445 sourceBody341_8

def sourceBody341_447 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_444 sourceBody341_446

def sourceBody341_448 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_447 sourceBody341_8

def sourceBody341_449 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_443 sourceBody341_448

def sourceBody341_450 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_449

def sourceBody341_451 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_442 sourceBody341_450

def sourceBody341_452 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_451

def sourceBody341_453 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_441 sourceBody341_452

def sourceBody341_454 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_453 sourceBody341_382

def sourceBody341_455 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.const 3#64)

def sourceBody341_456 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.const 20#64)

def sourceBody341_457 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody341_8, 341, 26)) (some 335) ([40, 28, 56]) (some (40, sourceBody341_308, 341, 27))

def sourceBody341_458 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_457 sourceBody341_5

def sourceBody341_459 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_458 sourceBody341_8

def sourceBody341_460 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_456 sourceBody341_459

def sourceBody341_461 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_305 sourceBody341_460

def sourceBody341_462 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_304 sourceBody341_461

def sourceBody341_463 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody341_8, 341, 28)) (some 336) ([40, 28]) (some (40, sourceBody341_308, 341, 29))

def sourceBody341_464 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_463 sourceBody341_5

def sourceBody341_465 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_464 sourceBody341_8

def sourceBody341_466 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_305 sourceBody341_465

def sourceBody341_467 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_304 sourceBody341_466

def sourceBody341_468 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.imm 0#64) sourceBody341_462 sourceBody341_467

def sourceBody341_469 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_468 sourceBody341_5

def sourceBody341_470 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_469 sourceBody341_8

def sourceBody341_471 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_303 sourceBody341_470

def sourceBody341_472 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_386 sourceBody341_471

def sourceBody341_473 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_455 sourceBody341_472

def sourceBody341_474 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_299 sourceBody341_473

def sourceBody341_475 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_454 sourceBody341_474

def sourceBody341_476 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 38, Flapjack.WordLangExpHOL.const 152#64])

def sourceBody341_477 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_476 sourceBody341_450

def sourceBody341_478 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_477

def sourceBody341_479 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_475 sourceBody341_478

def sourceBody341_480 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_479 sourceBody341_382

def sourceBody341_481 : WordLangProgHOL (BitVec 64) :=
.call (some (([32, 20, 48, 14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody341_8, 341, 30)) (some 332) ([40, 28, 56]) (some (40, sourceBody341_308, 341, 31))

def sourceBody341_482 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_481 sourceBody341_5

def sourceBody341_483 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_482 sourceBody341_8

def sourceBody341_484 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_327 sourceBody341_483

def sourceBody341_485 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_305 sourceBody341_484

def sourceBody341_486 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_304 sourceBody341_485

def sourceBody341_487 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_480 sourceBody341_486

def sourceBody341_488 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 38, Flapjack.WordLangExpHOL.const 160#64])

def sourceBody341_489 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_488 sourceBody341_373

def sourceBody341_490 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_489

def sourceBody341_491 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_487 sourceBody341_490

def sourceBody341_492 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_491 sourceBody341_382

def sourceBody341_493 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.var 30)

def sourceBody341_494 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 58)

def sourceBody341_495 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 56

def sourceBody341_496 : WordLangProgHOL (BitVec 64) :=
.call (some (([40, 28]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody341_8, 341, 32)) (some 334) ([56, 10]) (some (56, sourceBody341_495, 341, 33))

def sourceBody341_497 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_496 sourceBody341_5

def sourceBody341_498 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_497 sourceBody341_8

def sourceBody341_499 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_494 sourceBody341_498

def sourceBody341_500 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_493 sourceBody341_499

def sourceBody341_501 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 38, Flapjack.WordLangExpHOL.const 192#64])

def sourceBody341_502 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 40)

def sourceBody341_503 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 10)

def sourceBody341_504 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 56) 36

def sourceBody341_505 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_504 sourceBody341_8

def sourceBody341_506 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_503 sourceBody341_505

def sourceBody341_507 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_506 sourceBody341_8

def sourceBody341_508 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_502 sourceBody341_507

def sourceBody341_509 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_508

def sourceBody341_510 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_501 sourceBody341_509

def sourceBody341_511 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_510

def sourceBody341_512 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 38, Flapjack.WordLangExpHOL.const 200#64])

def sourceBody341_513 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_303 sourceBody341_507

def sourceBody341_514 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_513

def sourceBody341_515 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_512 sourceBody341_514

def sourceBody341_516 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_515

def sourceBody341_517 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_511 sourceBody341_516

def sourceBody341_518 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 58, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody341_519 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.var 56)

def sourceBody341_520 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_519 sourceBody341_8

def sourceBody341_521 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_520 sourceBody341_8

def sourceBody341_522 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_518 sourceBody341_521

def sourceBody341_523 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_522

def sourceBody341_524 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_517 sourceBody341_523

def sourceBody341_525 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 22)

def sourceBody341_526 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody341_527 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody341_528 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody341_529 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.reg 36) sourceBody341_527 sourceBody341_528

def sourceBody341_530 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_529 sourceBody341_5

def sourceBody341_531 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 30)

def sourceBody341_532 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 58)

def sourceBody341_533 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 36

def sourceBody341_534 : WordLangProgHOL (BitVec 64) :=
.call (some (([56, 10]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody341_8, 341, 34)) (some 337) ([36, 24]) (some (36, sourceBody341_533, 341, 35))

def sourceBody341_535 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_534 sourceBody341_5

def sourceBody341_536 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_535 sourceBody341_8

def sourceBody341_537 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_532 sourceBody341_536

def sourceBody341_538 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_531 sourceBody341_537

def sourceBody341_539 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.var 56)

def sourceBody341_540 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 10)

def sourceBody341_541 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 52

def sourceBody341_542 : WordLangProgHOL (BitVec 64) :=
.call (some (([36, 24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody341_8, 341, 36)) (some 338) ([52, 18]) (some (52, sourceBody341_541, 341, 37))

def sourceBody341_543 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_542 sourceBody341_5

def sourceBody341_544 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_543 sourceBody341_8

def sourceBody341_545 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_540 sourceBody341_544

def sourceBody341_546 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_539 sourceBody341_545

def sourceBody341_547 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 38, Flapjack.WordLangExpHOL.const 208#64])

def sourceBody341_548 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 36)

def sourceBody341_549 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 18)

def sourceBody341_550 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 52) 44

def sourceBody341_551 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_550 sourceBody341_8

def sourceBody341_552 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_549 sourceBody341_551

def sourceBody341_553 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_552 sourceBody341_8

def sourceBody341_554 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_548 sourceBody341_553

def sourceBody341_555 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_554

def sourceBody341_556 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_547 sourceBody341_555

def sourceBody341_557 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_556

def sourceBody341_558 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 38, Flapjack.WordLangExpHOL.const 216#64])

def sourceBody341_559 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 24)

def sourceBody341_560 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_559 sourceBody341_553

def sourceBody341_561 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_560

def sourceBody341_562 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_558 sourceBody341_561

def sourceBody341_563 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_562

def sourceBody341_564 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_557 sourceBody341_563

def sourceBody341_565 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 58, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody341_566 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.var 52)

def sourceBody341_567 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_566 sourceBody341_8

def sourceBody341_568 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_567 sourceBody341_8

def sourceBody341_569 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_565 sourceBody341_568

def sourceBody341_570 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_569

def sourceBody341_571 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_564 sourceBody341_570

def sourceBody341_572 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_546 sourceBody341_571

def sourceBody341_573 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_572

def sourceBody341_574 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_573

def sourceBody341_575 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_574

def sourceBody341_576 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_575

def sourceBody341_577 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_538 sourceBody341_576

def sourceBody341_578 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_577

def sourceBody341_579 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_578

def sourceBody341_580 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_579

def sourceBody341_581 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_580

def sourceBody341_582 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 24 (Flapjack.WordRegImm.imm 0#64) sourceBody341_581 sourceBody341_8

def sourceBody341_583 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_582 sourceBody341_5

def sourceBody341_584 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_583 sourceBody341_8

def sourceBody341_585 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_354 sourceBody341_584

def sourceBody341_586 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_530 sourceBody341_585

def sourceBody341_587 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_526 sourceBody341_586

def sourceBody341_588 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_525 sourceBody341_587

def sourceBody341_589 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_524 sourceBody341_588

def sourceBody341_590 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.const 3#64)

def sourceBody341_591 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 10 (Flapjack.WordRegImm.reg 36) sourceBody341_527 sourceBody341_528

def sourceBody341_592 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_591 sourceBody341_5

def sourceBody341_593 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody341_594 : WordLangProgHOL (BitVec 64) :=
.call (some (([32, 20, 48, 14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody341_8, 341, 38)) (some 332) ([56, 10, 36]) (some (56, sourceBody341_495, 341, 39))

def sourceBody341_595 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_594 sourceBody341_5

def sourceBody341_596 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_595 sourceBody341_8

def sourceBody341_597 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_593 sourceBody341_596

def sourceBody341_598 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_494 sourceBody341_597

def sourceBody341_599 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_493 sourceBody341_598

def sourceBody341_600 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 38, Flapjack.WordLangExpHOL.const 224#64])

def sourceBody341_601 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 32)

def sourceBody341_602 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 20)

def sourceBody341_603 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 48)

def sourceBody341_604 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.var 14)

def sourceBody341_605 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 56) 18

def sourceBody341_606 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_605 sourceBody341_8

def sourceBody341_607 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_540 sourceBody341_606

def sourceBody341_608 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 56, Flapjack.WordLangExpHOL.const 8#64])
  18

def sourceBody341_609 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_608 sourceBody341_8

def sourceBody341_610 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_548 sourceBody341_609

def sourceBody341_611 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 56, Flapjack.WordLangExpHOL.const 16#64])
  18

def sourceBody341_612 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_611 sourceBody341_8

def sourceBody341_613 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_559 sourceBody341_612

def sourceBody341_614 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 52)

def sourceBody341_615 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 56, Flapjack.WordLangExpHOL.const 24#64])
  18

def sourceBody341_616 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_615 sourceBody341_8

def sourceBody341_617 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_614 sourceBody341_616

def sourceBody341_618 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_617 sourceBody341_8

def sourceBody341_619 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_613 sourceBody341_618

def sourceBody341_620 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_610 sourceBody341_619

def sourceBody341_621 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_607 sourceBody341_620

def sourceBody341_622 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_604 sourceBody341_621

def sourceBody341_623 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_622

def sourceBody341_624 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_603 sourceBody341_623

def sourceBody341_625 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_624

def sourceBody341_626 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_602 sourceBody341_625

def sourceBody341_627 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_626

def sourceBody341_628 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_601 sourceBody341_627

def sourceBody341_629 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_628

def sourceBody341_630 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_600 sourceBody341_629

def sourceBody341_631 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_630

def sourceBody341_632 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_599 sourceBody341_631

def sourceBody341_633 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 58, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody341_634 : WordLangProgHOL (BitVec 64) :=
.call (some (([56, 10]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody341_8, 341, 40)) (some 337) ([36, 24]) (some (36, sourceBody341_533, 341, 41))

def sourceBody341_635 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_634 sourceBody341_5

def sourceBody341_636 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_635 sourceBody341_8

def sourceBody341_637 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_633 sourceBody341_636

def sourceBody341_638 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_531 sourceBody341_637

def sourceBody341_639 : WordLangProgHOL (BitVec 64) :=
.call (some (([36, 24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody341_8, 341, 42)) (some 339) ([52, 18]) (some (52, sourceBody341_541, 341, 43))

def sourceBody341_640 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_639 sourceBody341_5

def sourceBody341_641 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_640 sourceBody341_8

def sourceBody341_642 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_540 sourceBody341_641

def sourceBody341_643 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_539 sourceBody341_642

def sourceBody341_644 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 38, Flapjack.WordLangExpHOL.const 256#64])

def sourceBody341_645 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_644 sourceBody341_555

def sourceBody341_646 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_645

def sourceBody341_647 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 38, Flapjack.WordLangExpHOL.const 264#64])

def sourceBody341_648 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_647 sourceBody341_561

def sourceBody341_649 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_648

def sourceBody341_650 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_646 sourceBody341_649

def sourceBody341_651 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 58, Flapjack.WordLangExpHOL.const 2#64])

def sourceBody341_652 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_651 sourceBody341_568

def sourceBody341_653 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_652

def sourceBody341_654 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_650 sourceBody341_653

def sourceBody341_655 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_643 sourceBody341_654

def sourceBody341_656 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_655

def sourceBody341_657 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_656

def sourceBody341_658 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_657

def sourceBody341_659 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_658

def sourceBody341_660 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_638 sourceBody341_659

def sourceBody341_661 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_660

def sourceBody341_662 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_661

def sourceBody341_663 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_662

def sourceBody341_664 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_663

def sourceBody341_665 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_632 sourceBody341_664

def sourceBody341_666 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 24 (Flapjack.WordRegImm.imm 0#64) sourceBody341_665 sourceBody341_8

def sourceBody341_667 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_666 sourceBody341_5

def sourceBody341_668 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_667 sourceBody341_8

def sourceBody341_669 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_354 sourceBody341_668

def sourceBody341_670 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_592 sourceBody341_669

def sourceBody341_671 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_590 sourceBody341_670

def sourceBody341_672 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_525 sourceBody341_671

def sourceBody341_673 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_589 sourceBody341_672

def sourceBody341_674 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.const 4#64)

def sourceBody341_675 : WordLangProgHOL (BitVec 64) :=
.call (some (([56, 10]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody341_8, 341, 44)) (some 337) ([36, 24]) (some (36, sourceBody341_533, 341, 45))

def sourceBody341_676 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_675 sourceBody341_5

def sourceBody341_677 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_676 sourceBody341_8

def sourceBody341_678 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_532 sourceBody341_677

def sourceBody341_679 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_531 sourceBody341_678

def sourceBody341_680 : WordLangProgHOL (BitVec 64) :=
.call (some (([36, 24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody341_8, 341, 46)) (some 340) ([52, 18]) (some (52, sourceBody341_541, 341, 47))

def sourceBody341_681 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_680 sourceBody341_5

def sourceBody341_682 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_681 sourceBody341_8

def sourceBody341_683 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_540 sourceBody341_682

def sourceBody341_684 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_539 sourceBody341_683

def sourceBody341_685 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 38, Flapjack.WordLangExpHOL.const 272#64])

def sourceBody341_686 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_685 sourceBody341_555

def sourceBody341_687 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_686

def sourceBody341_688 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 38, Flapjack.WordLangExpHOL.const 280#64])

def sourceBody341_689 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_688 sourceBody341_561

def sourceBody341_690 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_689

def sourceBody341_691 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_687 sourceBody341_690

def sourceBody341_692 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_691 sourceBody341_570

def sourceBody341_693 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_684 sourceBody341_692

def sourceBody341_694 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_693

def sourceBody341_695 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_694

def sourceBody341_696 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_695

def sourceBody341_697 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_696

def sourceBody341_698 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_679 sourceBody341_697

def sourceBody341_699 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_698

def sourceBody341_700 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_699

def sourceBody341_701 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_700

def sourceBody341_702 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_701

def sourceBody341_703 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 24 (Flapjack.WordRegImm.imm 0#64) sourceBody341_702 sourceBody341_8

def sourceBody341_704 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_703 sourceBody341_5

def sourceBody341_705 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_704 sourceBody341_8

def sourceBody341_706 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_354 sourceBody341_705

def sourceBody341_707 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_592 sourceBody341_706

def sourceBody341_708 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_674 sourceBody341_707

def sourceBody341_709 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_525 sourceBody341_708

def sourceBody341_710 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_673 sourceBody341_709

def sourceBody341_711 : WordLangProgHOL (BitVec 64) :=
.call (some (([32, 20, 48, 14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody341_8, 341, 48)) (some 332) ([56, 10, 36]) (some (56, sourceBody341_495, 341, 49))

def sourceBody341_712 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_711 sourceBody341_5

def sourceBody341_713 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_712 sourceBody341_8

def sourceBody341_714 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_593 sourceBody341_713

def sourceBody341_715 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_494 sourceBody341_714

def sourceBody341_716 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_493 sourceBody341_715

def sourceBody341_717 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_710 sourceBody341_716

def sourceBody341_718 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 38, Flapjack.WordLangExpHOL.const 288#64])

def sourceBody341_719 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_718 sourceBody341_629

def sourceBody341_720 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_719

def sourceBody341_721 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_717 sourceBody341_720

def sourceBody341_722 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 58, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody341_723 : WordLangProgHOL (BitVec 64) :=
.call (some (([32, 20, 48, 14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody341_8, 341, 50)) (some 332) ([56, 10, 36]) (some (56, sourceBody341_495, 341, 51))

def sourceBody341_724 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_723 sourceBody341_5

def sourceBody341_725 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_724 sourceBody341_8

def sourceBody341_726 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_593 sourceBody341_725

def sourceBody341_727 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_722 sourceBody341_726

def sourceBody341_728 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_493 sourceBody341_727

def sourceBody341_729 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_721 sourceBody341_728

def sourceBody341_730 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 38, Flapjack.WordLangExpHOL.const 320#64])

def sourceBody341_731 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_730 sourceBody341_629

def sourceBody341_732 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_731

def sourceBody341_733 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_729 sourceBody341_732

def sourceBody341_734 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 58, Flapjack.WordLangExpHOL.const 2#64])

def sourceBody341_735 : WordLangProgHOL (BitVec 64) :=
.call (some (([32, 20, 48, 14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        Flapjack.Spt.ln)
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody341_8, 341, 52)) (some 332) ([56, 10, 36]) (some (56, sourceBody341_495, 341, 53))

def sourceBody341_736 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_735 sourceBody341_5

def sourceBody341_737 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_736 sourceBody341_8

def sourceBody341_738 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_593 sourceBody341_737

def sourceBody341_739 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_734 sourceBody341_738

def sourceBody341_740 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_493 sourceBody341_739

def sourceBody341_741 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_733 sourceBody341_740

def sourceBody341_742 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 38, Flapjack.WordLangExpHOL.const 352#64])

def sourceBody341_743 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_742 sourceBody341_629

def sourceBody341_744 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_743

def sourceBody341_745 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_741 sourceBody341_744

def sourceBody341_746 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.var 38)

def sourceBody341_747 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [56]

def sourceBody341_748 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_747 sourceBody341_8

def sourceBody341_749 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_746 sourceBody341_748

def sourceBody341_750 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_745 sourceBody341_749

def sourceBody341_751 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_500 sourceBody341_750

def sourceBody341_752 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_751

def sourceBody341_753 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_752

def sourceBody341_754 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_753

def sourceBody341_755 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_754

def sourceBody341_756 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_492 sourceBody341_755

def sourceBody341_757 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_756

def sourceBody341_758 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_757

def sourceBody341_759 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_758

def sourceBody341_760 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_759

def sourceBody341_761 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_760

def sourceBody341_762 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_761

def sourceBody341_763 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_762

def sourceBody341_764 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_763

def sourceBody341_765 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_298 sourceBody341_764

def sourceBody341_766 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_765

def sourceBody341_767 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_766

def sourceBody341_768 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_259 sourceBody341_767

def sourceBody341_769 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_768

def sourceBody341_770 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_258 sourceBody341_769

def sourceBody341_771 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_238 sourceBody341_770

def sourceBody341_772 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_771

def sourceBody341_773 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_237 sourceBody341_772

def sourceBody341_774 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_773

def sourceBody341_775 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_774

def sourceBody341_776 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_775

def sourceBody341_777 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_776

def sourceBody341_778 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_229 sourceBody341_777

def sourceBody341_779 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_67 sourceBody341_778

def sourceBody341_780 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_779

def sourceBody341_781 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_66 sourceBody341_780

def sourceBody341_782 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_781

def sourceBody341_783 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_782

def sourceBody341_784 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_783

def sourceBody341_785 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_784

def sourceBody341_786 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_785

def sourceBody341_787 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_786

def sourceBody341_788 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_787

def sourceBody341_789 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_788

def sourceBody341_790 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_789

def sourceBody341_791 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_65 sourceBody341_790

def sourceBody341_792 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_36 sourceBody341_791

def sourceBody341_793 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_792

def sourceBody341_794 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_8 sourceBody341_793

def sourceBody341_795 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_30 sourceBody341_794

def sourceBody341_796 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_29 sourceBody341_795

def sourceBody341_797 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody341_25 sourceBody341_796

def source341 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (341, 3, sourceBody341_797)
end InitECandidate.Proofs.WordStages
