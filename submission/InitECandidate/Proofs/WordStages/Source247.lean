import InitECandidate.Proofs.WordStages.Source231
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody247_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 4)

def sourceBody247_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody247_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody247_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody247_4 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 40 (Flapjack.WordRegImm.reg 26) sourceBody247_2 sourceBody247_3

def sourceBody247_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody247_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_4 sourceBody247_5

def sourceBody247_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.var 40)

def sourceBody247_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody247_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [12, 40]

def sourceBody247_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody247_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_9 sourceBody247_10

def sourceBody247_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_3 sourceBody247_11

def sourceBody247_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_8 sourceBody247_12

def sourceBody247_14 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 52 (Flapjack.WordRegImm.imm 0#64) sourceBody247_13 sourceBody247_10

def sourceBody247_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_14 sourceBody247_5

def sourceBody247_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_15 sourceBody247_10

def sourceBody247_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_7 sourceBody247_16

def sourceBody247_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_6 sourceBody247_17

def sourceBody247_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_1 sourceBody247_18

def sourceBody247_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_0 sourceBody247_19

def sourceBody247_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 4#64)

def sourceBody247_22 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 40 (Flapjack.WordRegImm.reg 26) sourceBody247_2 sourceBody247_3

def sourceBody247_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_22 sourceBody247_5

def sourceBody247_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.const 20#64)

def sourceBody247_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 40

def sourceBody247_26 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody247_10, 247, 2)) (some 245) ([40]) (some (40, sourceBody247_25, 247, 3))

def sourceBody247_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_26 sourceBody247_5

def sourceBody247_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_27 sourceBody247_10

def sourceBody247_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_24 sourceBody247_28

def sourceBody247_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_10 sourceBody247_29

def sourceBody247_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_10 sourceBody247_30

def sourceBody247_32 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 52 (Flapjack.WordRegImm.imm 0#64) sourceBody247_31 sourceBody247_10

def sourceBody247_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_32 sourceBody247_5

def sourceBody247_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_33 sourceBody247_10

def sourceBody247_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_7 sourceBody247_34

def sourceBody247_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_23 sourceBody247_35

def sourceBody247_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_21 sourceBody247_36

def sourceBody247_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_0 sourceBody247_37

def sourceBody247_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_20 sourceBody247_38

def sourceBody247_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 2)

def sourceBody247_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 12 (Flapjack.WordLangAddr.addr 12 0#64))

def sourceBody247_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody247_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 40 (Flapjack.WordLangAddr.addr 40 0#64))

def sourceBody247_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 2#64])

def sourceBody247_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 26 (Flapjack.WordLangAddr.addr 26 0#64))

def sourceBody247_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 3#64])

def sourceBody247_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 52 (Flapjack.WordLangAddr.addr 52 0#64))

def sourceBody247_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_47 sourceBody247_10

def sourceBody247_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_46 sourceBody247_48

def sourceBody247_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_45 sourceBody247_49

def sourceBody247_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_44 sourceBody247_50

def sourceBody247_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_43 sourceBody247_51

def sourceBody247_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_42 sourceBody247_52

def sourceBody247_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_41 sourceBody247_53

def sourceBody247_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_40 sourceBody247_54

def sourceBody247_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.or
    [Flapjack.WordLangExpHOL.var 12,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 40)
        (Flapjack.WordLangExpHOL.const 8#64),
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 26)
        (Flapjack.WordLangExpHOL.const 16#64),
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 52)
        (Flapjack.WordLangExpHOL.const 24#64)])

def sourceBody247_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 10)

def sourceBody247_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody247_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody247_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody247_61 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 22 (Flapjack.WordRegImm.reg 50) sourceBody247_59 sourceBody247_60

def sourceBody247_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_61 sourceBody247_5

def sourceBody247_63 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 3#64])

def sourceBody247_64 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody247_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody247_66 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody247_67 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 44 (Flapjack.WordRegImm.reg 30) sourceBody247_65 sourceBody247_66

def sourceBody247_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_67 sourceBody247_5

def sourceBody247_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 4)

def sourceBody247_70 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 10)

def sourceBody247_71 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody247_72 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody247_73 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 8 (Flapjack.WordRegImm.reg 34) sourceBody247_71 sourceBody247_72

def sourceBody247_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_73 sourceBody247_5

def sourceBody247_75 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody247_76 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.or
    [Flapjack.WordLangExpHOL.var 22, Flapjack.WordLangExpHOL.var 44, Flapjack.WordLangExpHOL.var 8])

def sourceBody247_77 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody247_78 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 48 (Flapjack.WordRegImm.reg 14) sourceBody247_77 sourceBody247_75

def sourceBody247_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_78 sourceBody247_5

def sourceBody247_80 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 48)

def sourceBody247_81 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 21#64)

def sourceBody247_82 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 22

def sourceBody247_83 : WordLangProgHOL (BitVec 64) :=
.call (some (([36]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody247_10, 247, 4)) (some 245) ([22]) (some (22, sourceBody247_82, 247, 5))

def sourceBody247_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_83 sourceBody247_5

def sourceBody247_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_84 sourceBody247_10

def sourceBody247_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_81 sourceBody247_85

def sourceBody247_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_10 sourceBody247_86

def sourceBody247_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_10 sourceBody247_87

def sourceBody247_89 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 42 (Flapjack.WordRegImm.imm 0#64) sourceBody247_88 sourceBody247_10

def sourceBody247_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_89 sourceBody247_5

def sourceBody247_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_90 sourceBody247_10

def sourceBody247_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_80 sourceBody247_91

def sourceBody247_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_79 sourceBody247_92

def sourceBody247_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_76 sourceBody247_93

def sourceBody247_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_75 sourceBody247_94

def sourceBody247_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_74 sourceBody247_95

def sourceBody247_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_70 sourceBody247_96

def sourceBody247_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_69 sourceBody247_97

def sourceBody247_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_68 sourceBody247_98

def sourceBody247_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_64 sourceBody247_99

def sourceBody247_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_63 sourceBody247_100

def sourceBody247_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_62 sourceBody247_101

def sourceBody247_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_58 sourceBody247_102

def sourceBody247_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_57 sourceBody247_103

def sourceBody247_105 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36
  (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr (Flapjack.WordLangExpHOL.var 10)
    (Flapjack.WordLangExpHOL.const 2#64))

def sourceBody247_106 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 6)

def sourceBody247_107 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 36)

def sourceBody247_108 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody247_109 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 50 (Flapjack.WordRegImm.reg 16) sourceBody247_108 sourceBody247_58

def sourceBody247_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_109 sourceBody247_5

def sourceBody247_111 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 50)

def sourceBody247_112 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.const 22#64)

def sourceBody247_113 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 50

def sourceBody247_114 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody247_10, 247, 6)) (some 245) ([50]) (some (50, sourceBody247_113, 247, 7))

def sourceBody247_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_114 sourceBody247_5

def sourceBody247_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_115 sourceBody247_10

def sourceBody247_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_112 sourceBody247_116

def sourceBody247_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_10 sourceBody247_117

def sourceBody247_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_10 sourceBody247_118

def sourceBody247_120 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 44 (Flapjack.WordRegImm.imm 0#64) sourceBody247_119 sourceBody247_10

def sourceBody247_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_120 sourceBody247_5

def sourceBody247_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_121 sourceBody247_10

def sourceBody247_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_111 sourceBody247_122

def sourceBody247_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_110 sourceBody247_123

def sourceBody247_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_107 sourceBody247_124

def sourceBody247_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_106 sourceBody247_125

def sourceBody247_127 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50
  (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 36)
    (Flapjack.WordLangExpHOL.const 4#64))

def sourceBody247_128 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody247_10, 247, 8)) (some 68) ([50]) (some (50, sourceBody247_113, 247, 9))

def sourceBody247_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_128 sourceBody247_5

def sourceBody247_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_129 sourceBody247_10

def sourceBody247_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_127 sourceBody247_130

def sourceBody247_132 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 10)

def sourceBody247_133 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 50)

def sourceBody247_134 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.var 36)

def sourceBody247_135 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody247_136 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.less) 30 (Flapjack.WordRegImm.reg 56) sourceBody247_135 sourceBody247_64

def sourceBody247_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_136 sourceBody247_5

def sourceBody247_138 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 30)

def sourceBody247_139 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 2,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 50)
        (Flapjack.WordLangExpHOL.const 2#64)])

def sourceBody247_140 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 44 (Flapjack.WordLangAddr.addr 44 0#64))

def sourceBody247_141 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 2,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 50)
        (Flapjack.WordLangExpHOL.const 2#64),
      Flapjack.WordLangExpHOL.const 1#64])

def sourceBody247_142 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 30 (Flapjack.WordLangAddr.addr 30 0#64))

def sourceBody247_143 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 2,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 50)
        (Flapjack.WordLangExpHOL.const 2#64),
      Flapjack.WordLangExpHOL.const 2#64])

def sourceBody247_144 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 56 (Flapjack.WordLangAddr.addr 56 0#64))

def sourceBody247_145 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 2,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 50)
        (Flapjack.WordLangExpHOL.const 2#64),
      Flapjack.WordLangExpHOL.const 3#64])

def sourceBody247_146 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 8 (Flapjack.WordLangAddr.addr 8 0#64))

def sourceBody247_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_146 sourceBody247_10

def sourceBody247_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_145 sourceBody247_147

def sourceBody247_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_144 sourceBody247_148

def sourceBody247_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_143 sourceBody247_149

def sourceBody247_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_142 sourceBody247_150

def sourceBody247_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_141 sourceBody247_151

def sourceBody247_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_140 sourceBody247_152

def sourceBody247_154 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_139 sourceBody247_153

def sourceBody247_155 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.or
    [Flapjack.WordLangExpHOL.var 44,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 30)
        (Flapjack.WordLangExpHOL.const 8#64),
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 56)
        (Flapjack.WordLangExpHOL.const 16#64),
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 8)
        (Flapjack.WordLangExpHOL.const 24#64)])

def sourceBody247_156 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 34)

def sourceBody247_157 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 10)

def sourceBody247_158 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 48 (Flapjack.WordRegImm.reg 14) sourceBody247_77 sourceBody247_75

def sourceBody247_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_158 sourceBody247_5

def sourceBody247_160 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 4)

def sourceBody247_161 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 34)

def sourceBody247_162 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody247_163 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody247_164 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 28 (Flapjack.WordRegImm.reg 54) sourceBody247_162 sourceBody247_163

def sourceBody247_165 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_164 sourceBody247_5

def sourceBody247_166 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 34)

def sourceBody247_167 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 16)

def sourceBody247_168 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody247_169 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody247_170 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 38 (Flapjack.WordRegImm.reg 24) sourceBody247_168 sourceBody247_169

def sourceBody247_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_170 sourceBody247_5

def sourceBody247_172 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody247_173 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.or
    [Flapjack.WordLangExpHOL.var 48, Flapjack.WordLangExpHOL.var 28, Flapjack.WordLangExpHOL.var 38])

def sourceBody247_174 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody247_175 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 18 (Flapjack.WordRegImm.reg 46) sourceBody247_174 sourceBody247_172

def sourceBody247_176 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_175 sourceBody247_5

def sourceBody247_177 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 18)

def sourceBody247_178 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.const 23#64)

def sourceBody247_179 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 48

def sourceBody247_180 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody247_10, 247, 10)) (some 245) ([48]) (some (48, sourceBody247_179, 247, 11))

def sourceBody247_181 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_180 sourceBody247_5

def sourceBody247_182 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_181 sourceBody247_10

def sourceBody247_183 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_178 sourceBody247_182

def sourceBody247_184 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_10 sourceBody247_183

def sourceBody247_185 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_10 sourceBody247_184

def sourceBody247_186 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 32 (Flapjack.WordRegImm.imm 0#64) sourceBody247_185 sourceBody247_10

def sourceBody247_187 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_186 sourceBody247_5

def sourceBody247_188 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_187 sourceBody247_10

def sourceBody247_189 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_177 sourceBody247_188

def sourceBody247_190 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_176 sourceBody247_189

def sourceBody247_191 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_173 sourceBody247_190

def sourceBody247_192 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_172 sourceBody247_191

def sourceBody247_193 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_171 sourceBody247_192

def sourceBody247_194 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_167 sourceBody247_193

def sourceBody247_195 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_166 sourceBody247_194

def sourceBody247_196 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_165 sourceBody247_195

def sourceBody247_197 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_161 sourceBody247_196

def sourceBody247_198 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_160 sourceBody247_197

def sourceBody247_199 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_159 sourceBody247_198

def sourceBody247_200 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_157 sourceBody247_199

def sourceBody247_201 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_156 sourceBody247_200

def sourceBody247_202 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 50)

def sourceBody247_203 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.less) 48 (Flapjack.WordRegImm.reg 14) sourceBody247_77 sourceBody247_75

def sourceBody247_204 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_203 sourceBody247_5

def sourceBody247_205 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 22,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.var 50, Flapjack.WordLangExpHOL.const 1#64])
        (Flapjack.WordLangExpHOL.const 4#64),
      Flapjack.WordLangExpHOL.const 8#64])

def sourceBody247_206 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 34, Flapjack.WordLangExpHOL.var 16])

def sourceBody247_207 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 48)

def sourceBody247_208 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 20) 14

def sourceBody247_209 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_208 sourceBody247_10

def sourceBody247_210 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_207 sourceBody247_209

def sourceBody247_211 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_210 sourceBody247_10

def sourceBody247_212 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_206 sourceBody247_211

def sourceBody247_213 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_10 sourceBody247_212

def sourceBody247_214 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_205 sourceBody247_213

def sourceBody247_215 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_10 sourceBody247_214

def sourceBody247_216 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 42 (Flapjack.WordRegImm.imm 0#64) sourceBody247_215 sourceBody247_10

def sourceBody247_217 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_216 sourceBody247_5

def sourceBody247_218 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_217 sourceBody247_10

def sourceBody247_219 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_80 sourceBody247_218

def sourceBody247_220 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_204 sourceBody247_219

def sourceBody247_221 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_202 sourceBody247_220

def sourceBody247_222 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_75 sourceBody247_221

def sourceBody247_223 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_201 sourceBody247_222

def sourceBody247_224 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 22,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 50)
        (Flapjack.WordLangExpHOL.const 4#64)])

def sourceBody247_225 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.var 34])

def sourceBody247_226 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_225 sourceBody247_211

def sourceBody247_227 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_10 sourceBody247_226

def sourceBody247_228 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_224 sourceBody247_227

def sourceBody247_229 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_10 sourceBody247_228

def sourceBody247_230 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_223 sourceBody247_229

def sourceBody247_231 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 34)

def sourceBody247_232 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_231 sourceBody247_10

def sourceBody247_233 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_232 sourceBody247_10

def sourceBody247_234 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_230 sourceBody247_233

def sourceBody247_235 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 50, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody247_236 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 20)

def sourceBody247_237 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_236 sourceBody247_10

def sourceBody247_238 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_237 sourceBody247_10

def sourceBody247_239 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_235 sourceBody247_238

def sourceBody247_240 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_10 sourceBody247_239

def sourceBody247_241 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_234 sourceBody247_240

def sourceBody247_242 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_155 sourceBody247_241

def sourceBody247_243 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_154 sourceBody247_242

def sourceBody247_244 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody247_245 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_243 sourceBody247_244

def sourceBody247_246 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody247_247 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.WordRegImm.imm 0#64) sourceBody247_245 sourceBody247_246

def sourceBody247_248 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_247 sourceBody247_5

def sourceBody247_249 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_248 sourceBody247_10

def sourceBody247_250 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_138 sourceBody247_249

def sourceBody247_251 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_137 sourceBody247_250

def sourceBody247_252 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_134 sourceBody247_251

def sourceBody247_253 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_133 sourceBody247_252

def sourceBody247_254 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
  PUnit.unit Flapjack.Spt.ln) sourceBody247_253 (Flapjack.Spt.bs
  (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody247_255 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_254 sourceBody247_5

def sourceBody247_256 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_5 sourceBody247_255

def sourceBody247_257 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 22,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.var 36, Flapjack.WordLangExpHOL.const 1#64])
        (Flapjack.WordLangExpHOL.const 4#64),
      Flapjack.WordLangExpHOL.const 8#64])

def sourceBody247_258 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.var 16])

def sourceBody247_259 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.var 30)

def sourceBody247_260 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 44) 56

def sourceBody247_261 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_260 sourceBody247_10

def sourceBody247_262 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_259 sourceBody247_261

def sourceBody247_263 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_262 sourceBody247_10

def sourceBody247_264 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_258 sourceBody247_263

def sourceBody247_265 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_10 sourceBody247_264

def sourceBody247_266 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_257 sourceBody247_265

def sourceBody247_267 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_10 sourceBody247_266

def sourceBody247_268 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_256 sourceBody247_267

def sourceBody247_269 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 22)

def sourceBody247_270 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 36)

def sourceBody247_271 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [44, 30]

def sourceBody247_272 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_271 sourceBody247_10

def sourceBody247_273 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_270 sourceBody247_272

def sourceBody247_274 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_269 sourceBody247_273

def sourceBody247_275 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_268 sourceBody247_274

def sourceBody247_276 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_132 sourceBody247_275

def sourceBody247_277 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_10 sourceBody247_276

def sourceBody247_278 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_58 sourceBody247_277

def sourceBody247_279 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_10 sourceBody247_278

def sourceBody247_280 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_131 sourceBody247_279

def sourceBody247_281 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_10 sourceBody247_280

def sourceBody247_282 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_10 sourceBody247_281

def sourceBody247_283 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_126 sourceBody247_282

def sourceBody247_284 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_105 sourceBody247_283

def sourceBody247_285 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_10 sourceBody247_284

def sourceBody247_286 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_104 sourceBody247_285

def sourceBody247_287 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_56 sourceBody247_286

def sourceBody247_288 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_55 sourceBody247_287

def sourceBody247_289 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody247_39 sourceBody247_288

def source247 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (247, 4, sourceBody247_289)
end InitECandidate.Proofs.WordStages
