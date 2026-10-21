import InitECandidate.Proofs.WordStages.Source296
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody312_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody312_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody312_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody312_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody312_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody312_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 8)

def sourceBody312_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 16#64)

def sourceBody312_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody312_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody312_9 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.less) 18 (Flapjack.WordRegImm.reg 34) sourceBody312_7 sourceBody312_8

def sourceBody312_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_9 sourceBody312_4

def sourceBody312_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 18)

def sourceBody312_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 32#64,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 8)
          (Flapjack.WordLangExpHOL.const 3#64)]))

def sourceBody312_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody312_14 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 18 (Flapjack.WordRegImm.reg 34) sourceBody312_7 sourceBody312_8

def sourceBody312_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_14 sourceBody312_4

def sourceBody312_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody312_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 26)

def sourceBody312_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_17 sourceBody312_0

def sourceBody312_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_18 sourceBody312_0

def sourceBody312_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_16 sourceBody312_19

def sourceBody312_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_0 sourceBody312_20

def sourceBody312_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 8)

def sourceBody312_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_22 sourceBody312_0

def sourceBody312_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_23 sourceBody312_0

def sourceBody312_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_21 sourceBody312_24

def sourceBody312_26 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.WordRegImm.imm 0#64) sourceBody312_25 sourceBody312_0

def sourceBody312_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_26 sourceBody312_4

def sourceBody312_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_27 sourceBody312_0

def sourceBody312_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_11 sourceBody312_28

def sourceBody312_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_15 sourceBody312_29

def sourceBody312_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_13 sourceBody312_30

def sourceBody312_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_12 sourceBody312_31

def sourceBody312_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody312_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 26)

def sourceBody312_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_34 sourceBody312_0

def sourceBody312_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_35 sourceBody312_0

def sourceBody312_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_33 sourceBody312_36

def sourceBody312_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_0 sourceBody312_37

def sourceBody312_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_32 sourceBody312_38

def sourceBody312_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody312_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_39 sourceBody312_40

def sourceBody312_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody312_43 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.WordRegImm.imm 0#64) sourceBody312_41 sourceBody312_42

def sourceBody312_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_43 sourceBody312_4

def sourceBody312_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_44 sourceBody312_0

def sourceBody312_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_11 sourceBody312_45

def sourceBody312_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_10 sourceBody312_46

def sourceBody312_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_6 sourceBody312_47

def sourceBody312_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_5 sourceBody312_48

def sourceBody312_50 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
    PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit Flapjack.Spt.ln) sourceBody312_49 (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
    PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody312_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_50 sourceBody312_4

def sourceBody312_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_4 sourceBody312_51

def sourceBody312_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 168#64]))

def sourceBody312_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 12)

def sourceBody312_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody312_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody312_57 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 34 (Flapjack.WordRegImm.reg 6) sourceBody312_56 sourceBody312_13

def sourceBody312_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_57 sourceBody312_4

def sourceBody312_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 34)

def sourceBody312_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 26)

def sourceBody312_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 12#64)

def sourceBody312_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 34

def sourceBody312_63 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
      PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody312_0, 312, 2)) (some 282) ([34]) (some (34, sourceBody312_62, 312, 3))

def sourceBody312_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_63 sourceBody312_4

def sourceBody312_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_64 sourceBody312_0

def sourceBody312_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_61 sourceBody312_65

def sourceBody312_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_0 sourceBody312_66

def sourceBody312_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_0 sourceBody312_67

def sourceBody312_69 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 24 (Flapjack.WordRegImm.imm 0#64) sourceBody312_68 sourceBody312_0

def sourceBody312_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_69 sourceBody312_4

def sourceBody312_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_70 sourceBody312_0

def sourceBody312_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_59 sourceBody312_71

def sourceBody312_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_58 sourceBody312_72

def sourceBody312_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_55 sourceBody312_73

def sourceBody312_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_60 sourceBody312_74

def sourceBody312_76 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 2)

def sourceBody312_77 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 160#64]))

def sourceBody312_78 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 26)

def sourceBody312_79 : WordLangProgHOL (BitVec 64) :=
.call (none) (some 292) ([0, 18, 34, 6, 24]) (none)

def sourceBody312_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_79 sourceBody312_0

def sourceBody312_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_78 sourceBody312_80

def sourceBody312_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_77 sourceBody312_81

def sourceBody312_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_13 sourceBody312_82

def sourceBody312_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_76 sourceBody312_83

def sourceBody312_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_75 sourceBody312_84

def sourceBody312_86 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 24 (Flapjack.WordRegImm.imm 0#64) sourceBody312_85 sourceBody312_0

def sourceBody312_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_86 sourceBody312_4

def sourceBody312_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_87 sourceBody312_0

def sourceBody312_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_59 sourceBody312_88

def sourceBody312_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_58 sourceBody312_89

def sourceBody312_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_55 sourceBody312_90

def sourceBody312_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_54 sourceBody312_91

def sourceBody312_93 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody312_94 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody312_95 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 34)

def sourceBody312_96 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody312_97 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 16 (Flapjack.WordRegImm.reg 32) sourceBody312_96 sourceBody312_94

def sourceBody312_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_97 sourceBody312_4

def sourceBody312_99 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 26)

def sourceBody312_100 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody312_101 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody312_102 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody312_103 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 28 (Flapjack.WordRegImm.reg 20) sourceBody312_101 sourceBody312_102

def sourceBody312_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_103 sourceBody312_4

def sourceBody312_105 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody312_106 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 28)

def sourceBody312_107 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody312_108 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 4 (Flapjack.WordRegImm.reg 22) sourceBody312_107 sourceBody312_105

def sourceBody312_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_108 sourceBody312_4

def sourceBody312_110 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and [Flapjack.WordLangExpHOL.var 16, Flapjack.WordLangExpHOL.var 4])

def sourceBody312_111 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 32#64,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 30)
          (Flapjack.WordLangExpHOL.const 3#64)]))

def sourceBody312_112 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 0#64]))

def sourceBody312_113 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody312_114 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody312_115 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 24 (Flapjack.WordRegImm.reg 16) sourceBody312_113 sourceBody312_114

def sourceBody312_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_115 sourceBody312_4

def sourceBody312_117 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 24)

def sourceBody312_118 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 2#64)

def sourceBody312_119 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 24

def sourceBody312_120 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody312_0, 312, 4)) (some 282) ([24]) (some (24, sourceBody312_119, 312, 5))

def sourceBody312_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_120 sourceBody312_4

def sourceBody312_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_121 sourceBody312_0

def sourceBody312_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_118 sourceBody312_122

def sourceBody312_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_0 sourceBody312_123

def sourceBody312_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_0 sourceBody312_124

def sourceBody312_126 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 32 (Flapjack.WordRegImm.imm 0#64) sourceBody312_125 sourceBody312_0

def sourceBody312_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_126 sourceBody312_4

def sourceBody312_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_127 sourceBody312_0

def sourceBody312_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_117 sourceBody312_128

def sourceBody312_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_116 sourceBody312_129

def sourceBody312_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_94 sourceBody312_130

def sourceBody312_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_59 sourceBody312_131

def sourceBody312_133 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 8#64)

def sourceBody312_134 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody312_0, 312, 6)) (some 68) ([24]) (some (24, sourceBody312_119, 312, 7))

def sourceBody312_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_134 sourceBody312_4

def sourceBody312_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_135 sourceBody312_0

def sourceBody312_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_133 sourceBody312_136

def sourceBody312_138 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 6)

def sourceBody312_139 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 30)

def sourceBody312_140 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.store8 16 (Flapjack.WordLangAddr.addr 24 0#64))

def sourceBody312_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_140 sourceBody312_0

def sourceBody312_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_139 sourceBody312_141

def sourceBody312_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_138 sourceBody312_142

def sourceBody312_144 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 34)

def sourceBody312_145 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.const 3#64)

def sourceBody312_146 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 16 (Flapjack.WordRegImm.reg 32) sourceBody312_96 sourceBody312_94

def sourceBody312_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_146 sourceBody312_4

def sourceBody312_148 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 16)

def sourceBody312_149 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 18)

def sourceBody312_150 : WordLangProgHOL (BitVec 64) :=
.call (none) (some 293) ([0, 24, 16, 32]) (none)

def sourceBody312_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_150 sourceBody312_0

def sourceBody312_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_149 sourceBody312_151

def sourceBody312_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_96 sourceBody312_152

def sourceBody312_154 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_138 sourceBody312_153

def sourceBody312_155 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.imm 0#64) sourceBody312_154 sourceBody312_0

def sourceBody312_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_155 sourceBody312_4

def sourceBody312_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_156 sourceBody312_0

def sourceBody312_158 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_148 sourceBody312_157

def sourceBody312_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_147 sourceBody312_158

def sourceBody312_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_145 sourceBody312_159

def sourceBody312_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_144 sourceBody312_160

def sourceBody312_162 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_143 sourceBody312_161

def sourceBody312_163 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 6)

def sourceBody312_164 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody312_165 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 32#64]))

def sourceBody312_166 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 40#64]))

def sourceBody312_167 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody312_168 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody312_0, 312, 8)) (some 288) ([16, 32, 10, 28]) (some (16, sourceBody312_167, 312, 9))

def sourceBody312_169 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_168 sourceBody312_4

def sourceBody312_170 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_169 sourceBody312_0

def sourceBody312_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_166 sourceBody312_170

def sourceBody312_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_165 sourceBody312_171

def sourceBody312_173 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_164 sourceBody312_172

def sourceBody312_174 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_163 sourceBody312_173

def sourceBody312_175 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody312_176 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody312_177 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 32 (Flapjack.WordRegImm.reg 10) sourceBody312_164 sourceBody312_176

def sourceBody312_178 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_177 sourceBody312_4

def sourceBody312_179 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 32)

def sourceBody312_180 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 24)

def sourceBody312_181 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.const 1#64,
      Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 40#64])])

def sourceBody312_182 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 48#64]))

def sourceBody312_183 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 56#64]))

def sourceBody312_184 : WordLangProgHOL (BitVec 64) :=
.call (none) (some 292) ([0, 16, 32, 10, 28]) (none)

def sourceBody312_185 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_184 sourceBody312_0

def sourceBody312_186 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_183 sourceBody312_185

def sourceBody312_187 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_182 sourceBody312_186

def sourceBody312_188 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_181 sourceBody312_187

def sourceBody312_189 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_180 sourceBody312_188

def sourceBody312_190 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 28 (Flapjack.WordRegImm.imm 0#64) sourceBody312_189 sourceBody312_0

def sourceBody312_191 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_190 sourceBody312_4

def sourceBody312_192 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_191 sourceBody312_0

def sourceBody312_193 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_179 sourceBody312_192

def sourceBody312_194 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_178 sourceBody312_193

def sourceBody312_195 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_175 sourceBody312_194

def sourceBody312_196 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_95 sourceBody312_195

def sourceBody312_197 : WordLangProgHOL (BitVec 64) :=
.call (none) (some 293) ([0, 16, 32, 10]) (none)

def sourceBody312_198 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_197 sourceBody312_0

def sourceBody312_199 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_182 sourceBody312_198

def sourceBody312_200 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_181 sourceBody312_199

def sourceBody312_201 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_180 sourceBody312_200

def sourceBody312_202 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_196 sourceBody312_201

def sourceBody312_203 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_174 sourceBody312_202

def sourceBody312_204 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_0 sourceBody312_203

def sourceBody312_205 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_0 sourceBody312_204

def sourceBody312_206 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_162 sourceBody312_205

def sourceBody312_207 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_137 sourceBody312_206

def sourceBody312_208 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_0 sourceBody312_207

def sourceBody312_209 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_0 sourceBody312_208

def sourceBody312_210 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_132 sourceBody312_209

def sourceBody312_211 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_112 sourceBody312_210

def sourceBody312_212 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_0 sourceBody312_211

def sourceBody312_213 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_111 sourceBody312_212

def sourceBody312_214 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_0 sourceBody312_213

def sourceBody312_215 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.WordRegImm.imm 0#64) sourceBody312_214 sourceBody312_0

def sourceBody312_216 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_215 sourceBody312_4

def sourceBody312_217 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_216 sourceBody312_0

def sourceBody312_218 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_110 sourceBody312_217

def sourceBody312_219 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_109 sourceBody312_218

def sourceBody312_220 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_106 sourceBody312_219

def sourceBody312_221 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_105 sourceBody312_220

def sourceBody312_222 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_104 sourceBody312_221

def sourceBody312_223 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_100 sourceBody312_222

def sourceBody312_224 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_99 sourceBody312_223

def sourceBody312_225 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_98 sourceBody312_224

def sourceBody312_226 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_95 sourceBody312_225

def sourceBody312_227 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_94 sourceBody312_226

def sourceBody312_228 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_58 sourceBody312_227

def sourceBody312_229 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_93 sourceBody312_228

def sourceBody312_230 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_54 sourceBody312_229

def sourceBody312_231 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_92 sourceBody312_230

def sourceBody312_232 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [18]

def sourceBody312_233 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_232 sourceBody312_0

def sourceBody312_234 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_76 sourceBody312_233

def sourceBody312_235 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_231 sourceBody312_234

def sourceBody312_236 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_53 sourceBody312_235

def sourceBody312_237 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_0 sourceBody312_236

def sourceBody312_238 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_52 sourceBody312_237

def sourceBody312_239 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_3 sourceBody312_238

def sourceBody312_240 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_0 sourceBody312_239

def sourceBody312_241 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_2 sourceBody312_240

def sourceBody312_242 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_0 sourceBody312_241

def sourceBody312_243 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_1 sourceBody312_242

def sourceBody312_244 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody312_0 sourceBody312_243

def source312 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (312, 2, sourceBody312_244)
end InitECandidate.Proofs.WordStages
