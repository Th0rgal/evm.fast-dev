import InitECandidate.Proofs.WordStages.Source281
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody297_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody297_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody297_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody297_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody297_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 4)

def sourceBody297_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 6)

def sourceBody297_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 32

def sourceBody297_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody297_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_0 sourceBody297_0

def sourceBody297_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_8 sourceBody297_0

def sourceBody297_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 3#64)

def sourceBody297_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody297_12 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody297_0, 297, 3)) (some 282) ([20]) (some (20, sourceBody297_11, 297, 4))

def sourceBody297_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_12 sourceBody297_7

def sourceBody297_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_13 sourceBody297_0

def sourceBody297_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_10 sourceBody297_14

def sourceBody297_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_0 sourceBody297_15

def sourceBody297_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_0 sourceBody297_16

def sourceBody297_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_9 sourceBody297_17

def sourceBody297_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_7 sourceBody297_18

def sourceBody297_20 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 32 (Flapjack.WordRegImm.imm 1#64) sourceBody297_6 sourceBody297_19

def sourceBody297_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_20 sourceBody297_7

def sourceBody297_22 : WordLangProgHOL (BitVec 64) :=
.call (some (([12, 36, 24, 48]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody297_0, 297, 2)) (some 162) ([32, 20]) (some (32, sourceBody297_21, 297, 5))

def sourceBody297_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_22 sourceBody297_7

def sourceBody297_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_23 sourceBody297_0

def sourceBody297_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_5 sourceBody297_24

def sourceBody297_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_4 sourceBody297_25

def sourceBody297_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 12)

def sourceBody297_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody297_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody297_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody297_31 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 20 (Flapjack.WordRegImm.reg 44) sourceBody297_29 sourceBody297_30

def sourceBody297_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_31 sourceBody297_7

def sourceBody297_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 20)

def sourceBody297_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 24)

def sourceBody297_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody297_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [32, 20]

def sourceBody297_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_36 sourceBody297_0

def sourceBody297_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_30 sourceBody297_37

def sourceBody297_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_35 sourceBody297_38

def sourceBody297_40 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 16 (Flapjack.WordRegImm.imm 0#64) sourceBody297_39 sourceBody297_0

def sourceBody297_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_40 sourceBody297_7

def sourceBody297_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_41 sourceBody297_0

def sourceBody297_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_33 sourceBody297_42

def sourceBody297_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_32 sourceBody297_43

def sourceBody297_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_28 sourceBody297_44

def sourceBody297_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_34 sourceBody297_45

def sourceBody297_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 4#64)

def sourceBody297_48 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody297_0, 297, 6)) (some 282) ([20]) (some (20, sourceBody297_11, 297, 7))

def sourceBody297_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_48 sourceBody297_7

def sourceBody297_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_49 sourceBody297_0

def sourceBody297_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_47 sourceBody297_50

def sourceBody297_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_0 sourceBody297_51

def sourceBody297_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_0 sourceBody297_52

def sourceBody297_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_46 sourceBody297_53

def sourceBody297_55 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 16 (Flapjack.WordRegImm.imm 0#64) sourceBody297_54 sourceBody297_0

def sourceBody297_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_55 sourceBody297_7

def sourceBody297_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_56 sourceBody297_0

def sourceBody297_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_33 sourceBody297_57

def sourceBody297_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_32 sourceBody297_58

def sourceBody297_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_28 sourceBody297_59

def sourceBody297_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_27 sourceBody297_60

def sourceBody297_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_26 sourceBody297_61

def sourceBody297_63 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 36)

def sourceBody297_64 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 24)

def sourceBody297_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 44

def sourceBody297_66 : WordLangProgHOL (BitVec 64) :=
.call (some (([32, 20]), ((Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody297_0, 297, 8)) (some 169) ([44, 16]) (some (44, sourceBody297_65, 297, 9))

def sourceBody297_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_66 sourceBody297_7

def sourceBody297_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_67 sourceBody297_0

def sourceBody297_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_64 sourceBody297_68

def sourceBody297_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_63 sourceBody297_69

def sourceBody297_71 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 32)

def sourceBody297_72 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 20)

def sourceBody297_73 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 2#64)

def sourceBody297_74 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody297_75 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody297_76 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 40 (Flapjack.WordRegImm.reg 28) sourceBody297_74 sourceBody297_75

def sourceBody297_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_76 sourceBody297_7

def sourceBody297_78 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.var 40)

def sourceBody297_79 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 44, Flapjack.WordLangExpHOL.const 0#64]))

def sourceBody297_80 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 44, Flapjack.WordLangExpHOL.const 0#64, Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody297_81 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody297_82 : WordLangProgHOL (BitVec 64) :=
.call (some (([16, 40, 28, 52]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
        PUnit.unit Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody297_0, 297, 10)) (some 161) ([8, 30]) (some (8, sourceBody297_81, 297, 11))

def sourceBody297_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_82 sourceBody297_7

def sourceBody297_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_83 sourceBody297_0

def sourceBody297_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_80 sourceBody297_84

def sourceBody297_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_79 sourceBody297_85

def sourceBody297_87 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 16)

def sourceBody297_88 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody297_89 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody297_90 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody297_91 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 30 (Flapjack.WordRegImm.reg 18) sourceBody297_89 sourceBody297_90

def sourceBody297_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_91 sourceBody297_7

def sourceBody297_93 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 30)

def sourceBody297_94 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 5#64)

def sourceBody297_95 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 30

def sourceBody297_96 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody297_0, 297, 12)) (some 282) ([30]) (some (30, sourceBody297_95, 297, 13))

def sourceBody297_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_96 sourceBody297_7

def sourceBody297_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_97 sourceBody297_0

def sourceBody297_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_94 sourceBody297_98

def sourceBody297_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_0 sourceBody297_99

def sourceBody297_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_0 sourceBody297_100

def sourceBody297_102 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 42 (Flapjack.WordRegImm.imm 0#64) sourceBody297_101 sourceBody297_0

def sourceBody297_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_102 sourceBody297_7

def sourceBody297_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_103 sourceBody297_0

def sourceBody297_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_93 sourceBody297_104

def sourceBody297_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_92 sourceBody297_105

def sourceBody297_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_88 sourceBody297_106

def sourceBody297_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_87 sourceBody297_107

def sourceBody297_109 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 40)

def sourceBody297_110 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 28)

def sourceBody297_111 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 42

def sourceBody297_112 : WordLangProgHOL (BitVec 64) :=
.call (some (([8, 30, 18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
        PUnit.unit Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody297_0, 297, 14)) (some 285) ([42, 14]) (some (42, sourceBody297_111, 297, 15))

def sourceBody297_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_112 sourceBody297_7

def sourceBody297_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_113 sourceBody297_0

def sourceBody297_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_110 sourceBody297_114

def sourceBody297_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_109 sourceBody297_115

def sourceBody297_117 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 18)

def sourceBody297_118 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody297_119 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody297_120 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody297_121 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.WordRegImm.reg 38) sourceBody297_119 sourceBody297_120

def sourceBody297_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_121 sourceBody297_7

def sourceBody297_123 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 14)

def sourceBody297_124 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 44, Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody297_125 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 44, Flapjack.WordLangExpHOL.const 16#64, Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody297_126 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 50

def sourceBody297_127 : WordLangProgHOL (BitVec 64) :=
.call (some (([42, 14, 38, 26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln)
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody297_0, 297, 16)) (some 161) ([50, 10]) (some (50, sourceBody297_126, 297, 17))

def sourceBody297_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_127 sourceBody297_7

def sourceBody297_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_128 sourceBody297_0

def sourceBody297_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_125 sourceBody297_129

def sourceBody297_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_124 sourceBody297_130

def sourceBody297_132 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 42)

def sourceBody297_133 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody297_134 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody297_135 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody297_136 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.reg 34) sourceBody297_134 sourceBody297_135

def sourceBody297_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_136 sourceBody297_7

def sourceBody297_138 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 10)

def sourceBody297_139 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 6#64)

def sourceBody297_140 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody297_141 : WordLangProgHOL (BitVec 64) :=
.call (some (([50]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit Flapjack.Spt.ln)
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody297_0, 297, 18)) (some 282) ([10]) (some (10, sourceBody297_140, 297, 19))

def sourceBody297_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_141 sourceBody297_7

def sourceBody297_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_142 sourceBody297_0

def sourceBody297_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_139 sourceBody297_143

def sourceBody297_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_0 sourceBody297_144

def sourceBody297_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_0 sourceBody297_145

def sourceBody297_147 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 22 (Flapjack.WordRegImm.imm 0#64) sourceBody297_146 sourceBody297_0

def sourceBody297_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_147 sourceBody297_7

def sourceBody297_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_148 sourceBody297_0

def sourceBody297_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_138 sourceBody297_149

def sourceBody297_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_137 sourceBody297_150

def sourceBody297_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_133 sourceBody297_151

def sourceBody297_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_132 sourceBody297_152

def sourceBody297_154 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 8)

def sourceBody297_155 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 30)

def sourceBody297_156 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 14)

def sourceBody297_157 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 38)

def sourceBody297_158 : WordLangProgHOL (BitVec 64) :=
.call (some (([50]), ((Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody297_0, 297, 20)) (some 292) ([10, 34, 22, 46]) (some (10, sourceBody297_140, 297, 21))

def sourceBody297_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_158 sourceBody297_7

def sourceBody297_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_159 sourceBody297_0

def sourceBody297_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_157 sourceBody297_160

def sourceBody297_162 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_156 sourceBody297_161

def sourceBody297_163 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_155 sourceBody297_162

def sourceBody297_164 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_154 sourceBody297_163

def sourceBody297_165 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 50, Flapjack.WordLangExpHOL.const 8#64])

def sourceBody297_166 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 4)

def sourceBody297_167 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 34)

def sourceBody297_168 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 10) 22

def sourceBody297_169 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_168 sourceBody297_0

def sourceBody297_170 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_167 sourceBody297_169

def sourceBody297_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_170 sourceBody297_0

def sourceBody297_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_166 sourceBody297_171

def sourceBody297_173 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_0 sourceBody297_172

def sourceBody297_174 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_165 sourceBody297_173

def sourceBody297_175 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_0 sourceBody297_174

def sourceBody297_176 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 50, Flapjack.WordLangExpHOL.const 16#64])

def sourceBody297_177 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 6)

def sourceBody297_178 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_177 sourceBody297_171

def sourceBody297_179 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_0 sourceBody297_178

def sourceBody297_180 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_176 sourceBody297_179

def sourceBody297_181 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_0 sourceBody297_180

def sourceBody297_182 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_175 sourceBody297_181

def sourceBody297_183 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 50)

def sourceBody297_184 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [10, 34]

def sourceBody297_185 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_184 sourceBody297_0

def sourceBody297_186 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_183 sourceBody297_185

def sourceBody297_187 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_135 sourceBody297_186

def sourceBody297_188 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_182 sourceBody297_187

def sourceBody297_189 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_164 sourceBody297_188

def sourceBody297_190 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_0 sourceBody297_189

def sourceBody297_191 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_0 sourceBody297_190

def sourceBody297_192 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_153 sourceBody297_191

def sourceBody297_193 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_131 sourceBody297_192

def sourceBody297_194 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_0 sourceBody297_193

def sourceBody297_195 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_0 sourceBody297_194

def sourceBody297_196 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_0 sourceBody297_195

def sourceBody297_197 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_0 sourceBody297_196

def sourceBody297_198 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_0 sourceBody297_197

def sourceBody297_199 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_0 sourceBody297_198

def sourceBody297_200 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_0 sourceBody297_199

def sourceBody297_201 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_0 sourceBody297_200

def sourceBody297_202 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 26 (Flapjack.WordRegImm.imm 0#64) sourceBody297_201 sourceBody297_0

def sourceBody297_203 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_202 sourceBody297_7

def sourceBody297_204 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_203 sourceBody297_0

def sourceBody297_205 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_123 sourceBody297_204

def sourceBody297_206 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_122 sourceBody297_205

def sourceBody297_207 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_118 sourceBody297_206

def sourceBody297_208 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_117 sourceBody297_207

def sourceBody297_209 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 30)

def sourceBody297_210 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 14 (Flapjack.WordRegImm.reg 38) sourceBody297_119 sourceBody297_120

def sourceBody297_211 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_210 sourceBody297_7

def sourceBody297_212 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 7#64)

def sourceBody297_213 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody297_214 : WordLangProgHOL (BitVec 64) :=
.call (some (([42]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln)
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
        PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody297_0, 297, 22)) (some 282) ([14]) (some (14, sourceBody297_213, 297, 23))

def sourceBody297_215 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_214 sourceBody297_7

def sourceBody297_216 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_215 sourceBody297_0

def sourceBody297_217 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_212 sourceBody297_216

def sourceBody297_218 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_0 sourceBody297_217

def sourceBody297_219 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_0 sourceBody297_218

def sourceBody297_220 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 26 (Flapjack.WordRegImm.imm 0#64) sourceBody297_219 sourceBody297_0

def sourceBody297_221 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_220 sourceBody297_7

def sourceBody297_222 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_221 sourceBody297_0

def sourceBody297_223 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_123 sourceBody297_222

def sourceBody297_224 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_211 sourceBody297_223

def sourceBody297_225 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_118 sourceBody297_224

def sourceBody297_226 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_209 sourceBody297_225

def sourceBody297_227 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_208 sourceBody297_226

def sourceBody297_228 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 88#64)

def sourceBody297_229 : WordLangProgHOL (BitVec 64) :=
.call (some (([42]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln)
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
        PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody297_0, 297, 24)) (some 74) ([14]) (some (14, sourceBody297_213, 297, 25))

def sourceBody297_230 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_229 sourceBody297_7

def sourceBody297_231 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_230 sourceBody297_0

def sourceBody297_232 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_228 sourceBody297_231

def sourceBody297_233 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 42, Flapjack.WordLangExpHOL.const 8#64])

def sourceBody297_234 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody297_235 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 38)

def sourceBody297_236 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 14) 26

def sourceBody297_237 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_236 sourceBody297_0

def sourceBody297_238 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_235 sourceBody297_237

def sourceBody297_239 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_238 sourceBody297_0

def sourceBody297_240 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_234 sourceBody297_239

def sourceBody297_241 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_0 sourceBody297_240

def sourceBody297_242 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_233 sourceBody297_241

def sourceBody297_243 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_0 sourceBody297_242

def sourceBody297_244 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 42, Flapjack.WordLangExpHOL.const 24#64])

def sourceBody297_245 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 44)

def sourceBody297_246 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_245 sourceBody297_239

def sourceBody297_247 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_0 sourceBody297_246

def sourceBody297_248 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_244 sourceBody297_247

def sourceBody297_249 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_0 sourceBody297_248

def sourceBody297_250 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_243 sourceBody297_249

def sourceBody297_251 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 42, Flapjack.WordLangExpHOL.const 48#64])

def sourceBody297_252 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 4)

def sourceBody297_253 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_252 sourceBody297_239

def sourceBody297_254 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_0 sourceBody297_253

def sourceBody297_255 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_251 sourceBody297_254

def sourceBody297_256 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_0 sourceBody297_255

def sourceBody297_257 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_250 sourceBody297_256

def sourceBody297_258 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 42, Flapjack.WordLangExpHOL.const 56#64])

def sourceBody297_259 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 6)

def sourceBody297_260 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_259 sourceBody297_239

def sourceBody297_261 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_0 sourceBody297_260

def sourceBody297_262 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_258 sourceBody297_261

def sourceBody297_263 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_0 sourceBody297_262

def sourceBody297_264 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_257 sourceBody297_263

def sourceBody297_265 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 42, Flapjack.WordLangExpHOL.const 64#64])

def sourceBody297_266 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 8)

def sourceBody297_267 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_266 sourceBody297_239

def sourceBody297_268 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_0 sourceBody297_267

def sourceBody297_269 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_265 sourceBody297_268

def sourceBody297_270 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_0 sourceBody297_269

def sourceBody297_271 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_264 sourceBody297_270

def sourceBody297_272 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 42, Flapjack.WordLangExpHOL.const 72#64])

def sourceBody297_273 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 30)

def sourceBody297_274 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_273 sourceBody297_239

def sourceBody297_275 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_0 sourceBody297_274

def sourceBody297_276 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_272 sourceBody297_275

def sourceBody297_277 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_0 sourceBody297_276

def sourceBody297_278 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_271 sourceBody297_277

def sourceBody297_279 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 42)

def sourceBody297_280 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [14, 38]

def sourceBody297_281 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_280 sourceBody297_0

def sourceBody297_282 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_279 sourceBody297_281

def sourceBody297_283 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_119 sourceBody297_282

def sourceBody297_284 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_278 sourceBody297_283

def sourceBody297_285 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_232 sourceBody297_284

def sourceBody297_286 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_0 sourceBody297_285

def sourceBody297_287 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_0 sourceBody297_286

def sourceBody297_288 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_227 sourceBody297_287

def sourceBody297_289 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_116 sourceBody297_288

def sourceBody297_290 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_0 sourceBody297_289

def sourceBody297_291 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_0 sourceBody297_290

def sourceBody297_292 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_0 sourceBody297_291

def sourceBody297_293 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_0 sourceBody297_292

def sourceBody297_294 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_0 sourceBody297_293

def sourceBody297_295 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_0 sourceBody297_294

def sourceBody297_296 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_108 sourceBody297_295

def sourceBody297_297 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_86 sourceBody297_296

def sourceBody297_298 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_0 sourceBody297_297

def sourceBody297_299 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_0 sourceBody297_298

def sourceBody297_300 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_0 sourceBody297_299

def sourceBody297_301 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_0 sourceBody297_300

def sourceBody297_302 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_0 sourceBody297_301

def sourceBody297_303 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_0 sourceBody297_302

def sourceBody297_304 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_0 sourceBody297_303

def sourceBody297_305 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_0 sourceBody297_304

def sourceBody297_306 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 52 (Flapjack.WordRegImm.imm 0#64) sourceBody297_305 sourceBody297_0

def sourceBody297_307 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_306 sourceBody297_7

def sourceBody297_308 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_307 sourceBody297_0

def sourceBody297_309 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_78 sourceBody297_308

def sourceBody297_310 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_77 sourceBody297_309

def sourceBody297_311 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_73 sourceBody297_310

def sourceBody297_312 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_72 sourceBody297_311

def sourceBody297_313 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 17#64)

def sourceBody297_314 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 40 (Flapjack.WordRegImm.reg 28) sourceBody297_74 sourceBody297_75

def sourceBody297_315 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_314 sourceBody297_7

def sourceBody297_316 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.const 4#64)

def sourceBody297_317 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 40

def sourceBody297_318 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
        PUnit.unit Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody297_0, 297, 26)) (some 282) ([40]) (some (40, sourceBody297_317, 297, 27))

def sourceBody297_319 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_318 sourceBody297_7

def sourceBody297_320 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_319 sourceBody297_0

def sourceBody297_321 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_316 sourceBody297_320

def sourceBody297_322 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_0 sourceBody297_321

def sourceBody297_323 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_0 sourceBody297_322

def sourceBody297_324 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 52 (Flapjack.WordRegImm.imm 0#64) sourceBody297_323 sourceBody297_0

def sourceBody297_325 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_324 sourceBody297_7

def sourceBody297_326 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_325 sourceBody297_0

def sourceBody297_327 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_78 sourceBody297_326

def sourceBody297_328 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_315 sourceBody297_327

def sourceBody297_329 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_313 sourceBody297_328

def sourceBody297_330 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_72 sourceBody297_329

def sourceBody297_331 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_312 sourceBody297_330

def sourceBody297_332 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
        PUnit.unit Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody297_0, 297, 28)) (some 294) ([]) (some (40, sourceBody297_317, 297, 29))

def sourceBody297_333 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_332 sourceBody297_7

def sourceBody297_334 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_333 sourceBody297_0

def sourceBody297_335 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 88#64)

def sourceBody297_336 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 28

def sourceBody297_337 : WordLangProgHOL (BitVec 64) :=
.call (some (([40]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
        PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody297_0, 297, 30)) (some 74) ([28]) (some (28, sourceBody297_336, 297, 31))

def sourceBody297_338 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_337 sourceBody297_7

def sourceBody297_339 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_338 sourceBody297_0

def sourceBody297_340 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_335 sourceBody297_339

def sourceBody297_341 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 40, Flapjack.WordLangExpHOL.const 8#64])

def sourceBody297_342 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.const 2#64)

def sourceBody297_343 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 52)

def sourceBody297_344 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 28) 8

def sourceBody297_345 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_344 sourceBody297_0

def sourceBody297_346 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_343 sourceBody297_345

def sourceBody297_347 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_346 sourceBody297_0

def sourceBody297_348 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_342 sourceBody297_347

def sourceBody297_349 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_0 sourceBody297_348

def sourceBody297_350 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_341 sourceBody297_349

def sourceBody297_351 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_0 sourceBody297_350

def sourceBody297_352 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 40, Flapjack.WordLangExpHOL.const 16#64])

def sourceBody297_353 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.var 16)

def sourceBody297_354 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_353 sourceBody297_347

def sourceBody297_355 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_0 sourceBody297_354

def sourceBody297_356 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_352 sourceBody297_355

def sourceBody297_357 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_0 sourceBody297_356

def sourceBody297_358 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_351 sourceBody297_357

def sourceBody297_359 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 40, Flapjack.WordLangExpHOL.const 24#64])

def sourceBody297_360 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.var 44)

def sourceBody297_361 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_360 sourceBody297_347

def sourceBody297_362 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_0 sourceBody297_361

def sourceBody297_363 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_359 sourceBody297_362

def sourceBody297_364 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_0 sourceBody297_363

def sourceBody297_365 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_358 sourceBody297_364

def sourceBody297_366 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 40, Flapjack.WordLangExpHOL.const 32#64])

def sourceBody297_367 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody297_368 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_367 sourceBody297_347

def sourceBody297_369 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_0 sourceBody297_368

def sourceBody297_370 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_366 sourceBody297_369

def sourceBody297_371 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_0 sourceBody297_370

def sourceBody297_372 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_365 sourceBody297_371

def sourceBody297_373 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 40, Flapjack.WordLangExpHOL.const 40#64])

def sourceBody297_374 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_373 sourceBody297_369

def sourceBody297_375 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_0 sourceBody297_374

def sourceBody297_376 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_372 sourceBody297_375

def sourceBody297_377 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 40, Flapjack.WordLangExpHOL.const 48#64])

def sourceBody297_378 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.var 4)

def sourceBody297_379 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_378 sourceBody297_347

def sourceBody297_380 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_0 sourceBody297_379

def sourceBody297_381 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_377 sourceBody297_380

def sourceBody297_382 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_0 sourceBody297_381

def sourceBody297_383 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_376 sourceBody297_382

def sourceBody297_384 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 40, Flapjack.WordLangExpHOL.const 56#64])

def sourceBody297_385 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.var 6)

def sourceBody297_386 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_385 sourceBody297_347

def sourceBody297_387 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_0 sourceBody297_386

def sourceBody297_388 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_384 sourceBody297_387

def sourceBody297_389 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_0 sourceBody297_388

def sourceBody297_390 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_383 sourceBody297_389

def sourceBody297_391 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody297_392 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [28, 52]

def sourceBody297_393 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_392 sourceBody297_0

def sourceBody297_394 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_78 sourceBody297_393

def sourceBody297_395 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_391 sourceBody297_394

def sourceBody297_396 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_390 sourceBody297_395

def sourceBody297_397 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_340 sourceBody297_396

def sourceBody297_398 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_0 sourceBody297_397

def sourceBody297_399 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_0 sourceBody297_398

def sourceBody297_400 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_334 sourceBody297_399

def sourceBody297_401 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_0 sourceBody297_400

def sourceBody297_402 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_0 sourceBody297_401

def sourceBody297_403 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_331 sourceBody297_402

def sourceBody297_404 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_71 sourceBody297_403

def sourceBody297_405 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_0 sourceBody297_404

def sourceBody297_406 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_70 sourceBody297_405

def sourceBody297_407 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_0 sourceBody297_406

def sourceBody297_408 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_0 sourceBody297_407

def sourceBody297_409 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_0 sourceBody297_408

def sourceBody297_410 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_0 sourceBody297_409

def sourceBody297_411 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_62 sourceBody297_410

def sourceBody297_412 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_0 sourceBody297_411

def sourceBody297_413 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_0 sourceBody297_412

def sourceBody297_414 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_0 sourceBody297_413

def sourceBody297_415 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_0 sourceBody297_414

def sourceBody297_416 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_3 sourceBody297_415

def sourceBody297_417 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_0 sourceBody297_416

def sourceBody297_418 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_2 sourceBody297_417

def sourceBody297_419 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_0 sourceBody297_418

def sourceBody297_420 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_1 sourceBody297_419

def sourceBody297_421 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody297_0 sourceBody297_420

def source297 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (297, 4, sourceBody297_421)
end InitECandidate.Proofs.WordStages
