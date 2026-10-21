import InitECandidate.Proofs.WordStages.Source587
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody603_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody603_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 120#64]))

def sourceBody603_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 128#64]))

def sourceBody603_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody603_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 8)

def sourceBody603_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody603_6 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 12 (Flapjack.WordRegImm.reg 20) sourceBody603_5 sourceBody603_3

def sourceBody603_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody603_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody603_6 sourceBody603_7

def sourceBody603_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 12)

def sourceBody603_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 18)

def sourceBody603_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 16 (Flapjack.WordLangAddr.addr 16 0#64))

def sourceBody603_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 16)

def sourceBody603_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 239#64)

def sourceBody603_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody603_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody603_16 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 20 (Flapjack.WordRegImm.reg 6) sourceBody603_14 sourceBody603_15

def sourceBody603_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody603_16 sourceBody603_7

def sourceBody603_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 20)

def sourceBody603_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 11#64)

def sourceBody603_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 16)

def sourceBody603_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody603_20 sourceBody603_0

def sourceBody603_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody603_21 sourceBody603_0

def sourceBody603_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody603_19 sourceBody603_22

def sourceBody603_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody603_0 sourceBody603_23

def sourceBody603_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 8#64)

def sourceBody603_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody603_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody603_25 sourceBody603_26

def sourceBody603_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody603_24 sourceBody603_27

def sourceBody603_29 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.WordRegImm.imm 0#64) sourceBody603_28 sourceBody603_0

def sourceBody603_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody603_29 sourceBody603_7

def sourceBody603_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody603_30 sourceBody603_0

def sourceBody603_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody603_18 sourceBody603_31

def sourceBody603_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody603_17 sourceBody603_32

def sourceBody603_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody603_13 sourceBody603_33

def sourceBody603_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody603_12 sourceBody603_34

def sourceBody603_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody603_11 sourceBody603_35

def sourceBody603_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody603_10 sourceBody603_36

def sourceBody603_38 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.WordRegImm.imm 0#64) sourceBody603_37 sourceBody603_0

def sourceBody603_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody603_38 sourceBody603_7

def sourceBody603_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody603_39 sourceBody603_0

def sourceBody603_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody603_9 sourceBody603_40

def sourceBody603_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody603_8 sourceBody603_41

def sourceBody603_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody603_4 sourceBody603_42

def sourceBody603_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody603_3 sourceBody603_43

def sourceBody603_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 65536#64)

def sourceBody603_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 4#64)

def sourceBody603_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody603_46 sourceBody603_22

def sourceBody603_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody603_0 sourceBody603_47

def sourceBody603_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody603_48 sourceBody603_27

def sourceBody603_50 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.WordRegImm.imm 0#64) sourceBody603_49 sourceBody603_0

def sourceBody603_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody603_50 sourceBody603_7

def sourceBody603_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody603_51 sourceBody603_0

def sourceBody603_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody603_9 sourceBody603_52

def sourceBody603_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody603_8 sourceBody603_53

def sourceBody603_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody603_4 sourceBody603_54

def sourceBody603_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody603_45 sourceBody603_55

def sourceBody603_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody603_44 sourceBody603_56

def sourceBody603_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 8)

def sourceBody603_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody603_60 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody603_0, 603, 2)) (some 461) ([12]) (some (12, sourceBody603_59, 603, 3))

def sourceBody603_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody603_60 sourceBody603_7

def sourceBody603_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody603_61 sourceBody603_0

def sourceBody603_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody603_58 sourceBody603_62

def sourceBody603_64 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 6#64)

def sourceBody603_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.longMul 14 14 20 6))

def sourceBody603_66 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 14)

def sourceBody603_67 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody603_68 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody603_0, 603, 4)) (some 466) ([10]) (some (20, sourceBody603_67, 603, 5))

def sourceBody603_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody603_68 sourceBody603_7

def sourceBody603_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody603_69 sourceBody603_0

def sourceBody603_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody603_66 sourceBody603_70

def sourceBody603_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody603_65 sourceBody603_71

def sourceBody603_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody603_64 sourceBody603_72

def sourceBody603_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody603_12 sourceBody603_73

def sourceBody603_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody603_0 sourceBody603_74

def sourceBody603_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody603_0 sourceBody603_75

def sourceBody603_77 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 1530#64)

def sourceBody603_78 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody603_0, 603, 6)) (some 467) ([10]) (some (20, sourceBody603_67, 603, 7))

def sourceBody603_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody603_78 sourceBody603_7

def sourceBody603_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody603_79 sourceBody603_0

def sourceBody603_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody603_66 sourceBody603_80

def sourceBody603_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody603_65 sourceBody603_81

def sourceBody603_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody603_77 sourceBody603_82

def sourceBody603_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody603_4 sourceBody603_83

def sourceBody603_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody603_0 sourceBody603_84

def sourceBody603_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody603_0 sourceBody603_85

def sourceBody603_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody603_76 sourceBody603_86

def sourceBody603_88 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 8#64])

def sourceBody603_89 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody603_0, 603, 8)) (some 68) ([20]) (some (20, sourceBody603_67, 603, 9))

def sourceBody603_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody603_89 sourceBody603_7

def sourceBody603_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody603_90 sourceBody603_0

def sourceBody603_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody603_88 sourceBody603_91

def sourceBody603_93 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 18)

def sourceBody603_94 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 8)

def sourceBody603_95 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody603_96 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody603_0, 603, 10)) (some 77) ([6, 14, 10]) (some (6, sourceBody603_95, 603, 11))

def sourceBody603_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody603_96 sourceBody603_7

def sourceBody603_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody603_97 sourceBody603_0

def sourceBody603_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody603_94 sourceBody603_98

def sourceBody603_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody603_93 sourceBody603_99

def sourceBody603_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody603_9 sourceBody603_100

def sourceBody603_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody603_0 sourceBody603_101

def sourceBody603_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody603_0 sourceBody603_102

def sourceBody603_104 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 32#64]))

def sourceBody603_105 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 12)

def sourceBody603_106 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody603_0, 603, 12)) (some 427) ([6, 14, 10]) (some (6, sourceBody603_95, 603, 13))

def sourceBody603_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody603_106 sourceBody603_7

def sourceBody603_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody603_107 sourceBody603_0

def sourceBody603_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody603_94 sourceBody603_108

def sourceBody603_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody603_105 sourceBody603_109

def sourceBody603_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody603_104 sourceBody603_110

def sourceBody603_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody603_0 sourceBody603_111

def sourceBody603_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody603_0 sourceBody603_112

def sourceBody603_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody603_103 sourceBody603_113

def sourceBody603_115 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [20]

def sourceBody603_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody603_115 sourceBody603_0

def sourceBody603_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody603_15 sourceBody603_116

def sourceBody603_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody603_114 sourceBody603_117

def sourceBody603_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody603_92 sourceBody603_118

def sourceBody603_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody603_0 sourceBody603_119

def sourceBody603_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody603_0 sourceBody603_120

def sourceBody603_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody603_87 sourceBody603_121

def sourceBody603_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody603_63 sourceBody603_122

def sourceBody603_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody603_0 sourceBody603_123

def sourceBody603_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody603_0 sourceBody603_124

def sourceBody603_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody603_57 sourceBody603_125

def sourceBody603_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody603_2 sourceBody603_126

def sourceBody603_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody603_0 sourceBody603_127

def sourceBody603_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody603_1 sourceBody603_128

def sourceBody603_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody603_0 sourceBody603_129

def source603 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (603, 3, sourceBody603_130)
end InitECandidate.Proofs.WordStages
