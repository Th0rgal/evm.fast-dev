import InitECandidate.Proofs.WordStages.Source833
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody849_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody849_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody849_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([34]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody849_0, 849, 2)) (some 69) ([]) (some (10, sourceBody849_1, 849, 3))

def sourceBody849_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody849_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_2 sourceBody849_3

def sourceBody849_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_4 sourceBody849_0

def sourceBody849_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 2)

def sourceBody849_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody849_8 : WordLangProgHOL (BitVec 64) :=
.call (some (([10, 28]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody849_0, 849, 4)) (some 272) ([18]) (some (18, sourceBody849_7, 849, 5))

def sourceBody849_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_8 sourceBody849_3

def sourceBody849_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_9 sourceBody849_0

def sourceBody849_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_6 sourceBody849_10

def sourceBody849_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 34)

def sourceBody849_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 40

def sourceBody849_14 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody849_0, 849, 6)) (some 70) ([40]) (some (40, sourceBody849_13, 849, 7))

def sourceBody849_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_14 sourceBody849_3

def sourceBody849_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_15 sourceBody849_0

def sourceBody849_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_12 sourceBody849_16

def sourceBody849_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_0 sourceBody849_17

def sourceBody849_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_0 sourceBody849_18

def sourceBody849_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 28)

def sourceBody849_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 32#64]))

def sourceBody849_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 40#64]))

def sourceBody849_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody849_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody849_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 16)

def sourceBody849_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 8)

def sourceBody849_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody849_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody849_29 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.less) 12 (Flapjack.WordRegImm.reg 32) sourceBody849_27 sourceBody849_28

def sourceBody849_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_29 sourceBody849_3

def sourceBody849_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 12)

def sourceBody849_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 40,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 16)
          (Flapjack.WordLangExpHOL.const 4#64),
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody849_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 38)

def sourceBody849_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody849_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody849_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody849_37 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 22 (Flapjack.WordRegImm.reg 44) sourceBody849_35 sourceBody849_36

def sourceBody849_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_37 sourceBody849_3

def sourceBody849_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 22)

def sourceBody849_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 40,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 16)
          (Flapjack.WordLangExpHOL.const 4#64)]))

def sourceBody849_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 32 (Flapjack.WordLangAddr.addr 32 0#64))

def sourceBody849_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 32)

def sourceBody849_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_42 sourceBody849_0

def sourceBody849_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_41 sourceBody849_43

def sourceBody849_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_40 sourceBody849_44

def sourceBody849_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_45 sourceBody849_0

def sourceBody849_47 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.WordRegImm.imm 0#64) sourceBody849_46 sourceBody849_0

def sourceBody849_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_47 sourceBody849_3

def sourceBody849_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_48 sourceBody849_0

def sourceBody849_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_39 sourceBody849_49

def sourceBody849_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_38 sourceBody849_50

def sourceBody849_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_34 sourceBody849_51

def sourceBody849_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_33 sourceBody849_52

def sourceBody849_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 38)

def sourceBody849_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 38)

def sourceBody849_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody849_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody849_58 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 44 (Flapjack.WordRegImm.reg 6) sourceBody849_57 sourceBody849_34

def sourceBody849_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_58 sourceBody849_3

def sourceBody849_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 12)

def sourceBody849_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.const 192#64)

def sourceBody849_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody849_63 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody849_64 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 14 (Flapjack.WordRegImm.reg 36) sourceBody849_62 sourceBody849_63

def sourceBody849_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_64 sourceBody849_3

def sourceBody849_66 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody849_67 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.or [Flapjack.WordLangExpHOL.var 44, Flapjack.WordLangExpHOL.var 14])

def sourceBody849_68 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody849_69 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 30 (Flapjack.WordRegImm.reg 20) sourceBody849_68 sourceBody849_66

def sourceBody849_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_69 sourceBody849_3

def sourceBody849_71 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 30)

def sourceBody849_72 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 22

def sourceBody849_73 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody849_0, 849, 8)) (some 179) ([22, 44]) (some (22, sourceBody849_72, 849, 9))

def sourceBody849_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_73 sourceBody849_3

def sourceBody849_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_74 sourceBody849_0

def sourceBody849_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_55 sourceBody849_75

def sourceBody849_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_31 sourceBody849_76

def sourceBody849_78 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 42 (Flapjack.WordRegImm.imm 0#64) sourceBody849_77 sourceBody849_0

def sourceBody849_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_78 sourceBody849_3

def sourceBody849_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_79 sourceBody849_0

def sourceBody849_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_71 sourceBody849_80

def sourceBody849_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_70 sourceBody849_81

def sourceBody849_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_67 sourceBody849_82

def sourceBody849_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_66 sourceBody849_83

def sourceBody849_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_65 sourceBody849_84

def sourceBody849_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_61 sourceBody849_85

def sourceBody849_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_60 sourceBody849_86

def sourceBody849_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_59 sourceBody849_87

def sourceBody849_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_56 sourceBody849_88

def sourceBody849_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_55 sourceBody849_89

def sourceBody849_91 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 26, Flapjack.WordLangExpHOL.var 32])

def sourceBody849_92 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 22)

def sourceBody849_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_92 sourceBody849_0

def sourceBody849_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_93 sourceBody849_0

def sourceBody849_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_91 sourceBody849_94

def sourceBody849_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_0 sourceBody849_95

def sourceBody849_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_90 sourceBody849_96

def sourceBody849_98 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 16, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody849_99 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 22)

def sourceBody849_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_99 sourceBody849_0

def sourceBody849_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_100 sourceBody849_0

def sourceBody849_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_98 sourceBody849_101

def sourceBody849_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_0 sourceBody849_102

def sourceBody849_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_97 sourceBody849_103

def sourceBody849_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_54 sourceBody849_104

def sourceBody849_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_0 sourceBody849_105

def sourceBody849_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_53 sourceBody849_106

def sourceBody849_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_28 sourceBody849_107

def sourceBody849_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_0 sourceBody849_108

def sourceBody849_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_32 sourceBody849_109

def sourceBody849_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_0 sourceBody849_110

def sourceBody849_112 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody849_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_111 sourceBody849_112

def sourceBody849_114 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody849_115 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 22 (Flapjack.WordRegImm.imm 0#64) sourceBody849_113 sourceBody849_114

def sourceBody849_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_115 sourceBody849_3

def sourceBody849_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_116 sourceBody849_0

def sourceBody849_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_31 sourceBody849_117

def sourceBody849_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_30 sourceBody849_118

def sourceBody849_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_26 sourceBody849_119

def sourceBody849_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_25 sourceBody849_120

def sourceBody849_122 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit))))
  PUnit.unit Flapjack.Spt.ln) sourceBody849_121 (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody849_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_122 sourceBody849_3

def sourceBody849_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_3 sourceBody849_123

def sourceBody849_125 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 26)

def sourceBody849_126 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody849_127 : WordLangProgHOL (BitVec 64) :=
.call (some (([38]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody849_0, 849, 10)) (some 180) ([12]) (some (12, sourceBody849_126, 849, 11))

def sourceBody849_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_127 sourceBody849_3

def sourceBody849_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_128 sourceBody849_0

def sourceBody849_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_125 sourceBody849_129

def sourceBody849_131 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.var 38, Flapjack.WordLangExpHOL.var 26])

def sourceBody849_132 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 12)

def sourceBody849_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_132 sourceBody849_0

def sourceBody849_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_133 sourceBody849_0

def sourceBody849_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_131 sourceBody849_134

def sourceBody849_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_0 sourceBody849_135

def sourceBody849_137 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody849_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_137 sourceBody849_134

def sourceBody849_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_0 sourceBody849_138

def sourceBody849_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_136 sourceBody849_139

def sourceBody849_141 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 56#64]))

def sourceBody849_142 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody849_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_24 sourceBody849_0

def sourceBody849_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_143 sourceBody849_0

def sourceBody849_145 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 16)

def sourceBody849_146 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 12)

def sourceBody849_147 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.less) 44 (Flapjack.WordRegImm.reg 6) sourceBody849_57 sourceBody849_34

def sourceBody849_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_147 sourceBody849_3

def sourceBody849_149 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 44)

def sourceBody849_150 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 44#64)

def sourceBody849_151 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.longMul 24 24 44 6))

def sourceBody849_152 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 48#64]),
      Flapjack.WordLangExpHOL.var 24])

def sourceBody849_153 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 44

def sourceBody849_154 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody849_0, 849, 12)) (some 840) ([14]) (some (44, sourceBody849_153, 849, 13))

def sourceBody849_155 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_154 sourceBody849_3

def sourceBody849_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_155 sourceBody849_0

def sourceBody849_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_152 sourceBody849_156

def sourceBody849_158 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_151 sourceBody849_157

def sourceBody849_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_150 sourceBody849_158

def sourceBody849_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_145 sourceBody849_159

def sourceBody849_161 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 32, Flapjack.WordLangExpHOL.var 22])

def sourceBody849_162 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 44)

def sourceBody849_163 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_162 sourceBody849_0

def sourceBody849_164 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_163 sourceBody849_0

def sourceBody849_165 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_161 sourceBody849_164

def sourceBody849_166 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_0 sourceBody849_165

def sourceBody849_167 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 16, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody849_168 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 44)

def sourceBody849_169 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_168 sourceBody849_0

def sourceBody849_170 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_169 sourceBody849_0

def sourceBody849_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_167 sourceBody849_170

def sourceBody849_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_0 sourceBody849_171

def sourceBody849_173 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_166 sourceBody849_172

def sourceBody849_174 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_160 sourceBody849_173

def sourceBody849_175 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_0 sourceBody849_174

def sourceBody849_176 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_0 sourceBody849_175

def sourceBody849_177 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_176 sourceBody849_112

def sourceBody849_178 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 24 (Flapjack.WordRegImm.imm 0#64) sourceBody849_177 sourceBody849_114

def sourceBody849_179 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_178 sourceBody849_3

def sourceBody849_180 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_179 sourceBody849_0

def sourceBody849_181 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_149 sourceBody849_180

def sourceBody849_182 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_148 sourceBody849_181

def sourceBody849_183 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_146 sourceBody849_182

def sourceBody849_184 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_145 sourceBody849_183

def sourceBody849_185 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
  PUnit.unit Flapjack.Spt.ln) sourceBody849_184 (Flapjack.Spt.bs
  (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody849_186 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_185 sourceBody849_3

def sourceBody849_187 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_3 sourceBody849_186

def sourceBody849_188 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_144 sourceBody849_187

def sourceBody849_189 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 32)

def sourceBody849_190 : WordLangProgHOL (BitVec 64) :=
.call (some (([38]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody849_0, 849, 14)) (some 180) ([22]) (some (22, sourceBody849_72, 849, 15))

def sourceBody849_191 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_190 sourceBody849_3

def sourceBody849_192 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_191 sourceBody849_0

def sourceBody849_193 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_189 sourceBody849_192

def sourceBody849_194 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_188 sourceBody849_193

def sourceBody849_195 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.var 38, Flapjack.WordLangExpHOL.var 32])

def sourceBody849_196 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 22)

def sourceBody849_197 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_196 sourceBody849_0

def sourceBody849_198 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_197 sourceBody849_0

def sourceBody849_199 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_195 sourceBody849_198

def sourceBody849_200 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_0 sourceBody849_199

def sourceBody849_201 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_194 sourceBody849_200

def sourceBody849_202 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 18)

def sourceBody849_203 : WordLangProgHOL (BitVec 64) :=
.call (some (([38]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody849_0, 849, 16)) (some 180) ([22]) (some (22, sourceBody849_72, 849, 17))

def sourceBody849_204 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_203 sourceBody849_3

def sourceBody849_205 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_204 sourceBody849_0

def sourceBody849_206 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_202 sourceBody849_205

def sourceBody849_207 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_201 sourceBody849_206

def sourceBody849_208 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.var 38])

def sourceBody849_209 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [22]

def sourceBody849_210 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_209 sourceBody849_0

def sourceBody849_211 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_208 sourceBody849_210

def sourceBody849_212 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_207 sourceBody849_211

def sourceBody849_213 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_142 sourceBody849_212

def sourceBody849_214 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_0 sourceBody849_213

def sourceBody849_215 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_141 sourceBody849_214

def sourceBody849_216 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_0 sourceBody849_215

def sourceBody849_217 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_140 sourceBody849_216

def sourceBody849_218 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_130 sourceBody849_217

def sourceBody849_219 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_0 sourceBody849_218

def sourceBody849_220 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_0 sourceBody849_219

def sourceBody849_221 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_124 sourceBody849_220

def sourceBody849_222 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_24 sourceBody849_221

def sourceBody849_223 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_0 sourceBody849_222

def sourceBody849_224 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_23 sourceBody849_223

def sourceBody849_225 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_0 sourceBody849_224

def sourceBody849_226 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_22 sourceBody849_225

def sourceBody849_227 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_0 sourceBody849_226

def sourceBody849_228 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_21 sourceBody849_227

def sourceBody849_229 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_0 sourceBody849_228

def sourceBody849_230 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_20 sourceBody849_229

def sourceBody849_231 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_0 sourceBody849_230

def sourceBody849_232 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_19 sourceBody849_231

def sourceBody849_233 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_11 sourceBody849_232

def sourceBody849_234 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_0 sourceBody849_233

def sourceBody849_235 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_0 sourceBody849_234

def sourceBody849_236 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_0 sourceBody849_235

def sourceBody849_237 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_0 sourceBody849_236

def sourceBody849_238 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_5 sourceBody849_237

def sourceBody849_239 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_0 sourceBody849_238

def sourceBody849_240 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody849_0 sourceBody849_239

def source849 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (849, 3, sourceBody849_240)
end InitECandidate.Proofs.WordStages
