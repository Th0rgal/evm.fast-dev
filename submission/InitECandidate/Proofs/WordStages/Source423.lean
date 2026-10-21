import InitECandidate.Proofs.WordStages.Source407
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody423_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody423_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 2)

def sourceBody423_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody423_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([40]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody423_0, 423, 2)) (some 403) ([16]) (some (16, sourceBody423_2, 423, 3))

def sourceBody423_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody423_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_3 sourceBody423_4

def sourceBody423_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_5 sourceBody423_0

def sourceBody423_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_1 sourceBody423_6

def sourceBody423_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 40, Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody423_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 40, Flapjack.WordLangExpHOL.const 8#64],
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody423_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 40, Flapjack.WordLangExpHOL.const 8#64],
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody423_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 40, Flapjack.WordLangExpHOL.const 8#64],
        Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody423_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 6)

def sourceBody423_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 8)

def sourceBody423_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 10)

def sourceBody423_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 12)

def sourceBody423_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 30

def sourceBody423_17 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody423_0, 423, 4)) (some 106) ([30, 24, 38, 20, 34, 26, 42, 14]) (some (30, sourceBody423_16, 423, 5))

def sourceBody423_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_17 sourceBody423_4

def sourceBody423_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_18 sourceBody423_0

def sourceBody423_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_15 sourceBody423_19

def sourceBody423_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_14 sourceBody423_20

def sourceBody423_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_13 sourceBody423_21

def sourceBody423_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_12 sourceBody423_22

def sourceBody423_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_11 sourceBody423_23

def sourceBody423_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_10 sourceBody423_24

def sourceBody423_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_9 sourceBody423_25

def sourceBody423_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_8 sourceBody423_26

def sourceBody423_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 16)

def sourceBody423_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody423_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody423_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody423_32 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 24 (Flapjack.WordRegImm.reg 38) sourceBody423_30 sourceBody423_31

def sourceBody423_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_32 sourceBody423_4

def sourceBody423_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 24)

def sourceBody423_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 4#64)

def sourceBody423_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 30)

def sourceBody423_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_36 sourceBody423_0

def sourceBody423_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_37 sourceBody423_0

def sourceBody423_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_35 sourceBody423_38

def sourceBody423_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_0 sourceBody423_39

def sourceBody423_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 7#64)

def sourceBody423_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_41 sourceBody423_16

def sourceBody423_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_40 sourceBody423_42

def sourceBody423_44 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 20 (Flapjack.WordRegImm.imm 0#64) sourceBody423_43 sourceBody423_0

def sourceBody423_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_44 sourceBody423_4

def sourceBody423_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_45 sourceBody423_0

def sourceBody423_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_34 sourceBody423_46

def sourceBody423_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_33 sourceBody423_47

def sourceBody423_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_29 sourceBody423_48

def sourceBody423_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_28 sourceBody423_49

def sourceBody423_51 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 40)

def sourceBody423_52 : WordLangProgHOL (BitVec 64) :=
.call (some (([40]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody423_0, 423, 6)) (some 391) ([30]) (some (30, sourceBody423_16, 423, 7))

def sourceBody423_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_52 sourceBody423_4

def sourceBody423_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_53 sourceBody423_0

def sourceBody423_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_51 sourceBody423_54

def sourceBody423_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_50 sourceBody423_55

def sourceBody423_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 40, Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody423_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 40, Flapjack.WordLangExpHOL.const 8#64],
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody423_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 40, Flapjack.WordLangExpHOL.const 8#64],
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody423_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 40, Flapjack.WordLangExpHOL.const 8#64],
        Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody423_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 6)

def sourceBody423_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 8)

def sourceBody423_63 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 10)

def sourceBody423_64 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 12)

def sourceBody423_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 34

def sourceBody423_66 : WordLangProgHOL (BitVec 64) :=
.call (some (([30, 24, 38, 20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody423_0, 423, 8)) (some 117) ([34, 26, 42, 14, 28, 22, 36, 18]) (some (34, sourceBody423_65, 423, 9))

def sourceBody423_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_66 sourceBody423_4

def sourceBody423_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_67 sourceBody423_0

def sourceBody423_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_64 sourceBody423_68

def sourceBody423_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_63 sourceBody423_69

def sourceBody423_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_62 sourceBody423_70

def sourceBody423_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_61 sourceBody423_71

def sourceBody423_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_60 sourceBody423_72

def sourceBody423_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_59 sourceBody423_73

def sourceBody423_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_58 sourceBody423_74

def sourceBody423_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_57 sourceBody423_75

def sourceBody423_77 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 40, Flapjack.WordLangExpHOL.const 8#64])

def sourceBody423_78 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 30)

def sourceBody423_79 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 24)

def sourceBody423_80 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 38)

def sourceBody423_81 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 20)

def sourceBody423_82 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 26)

def sourceBody423_83 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 34) 22

def sourceBody423_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_83 sourceBody423_0

def sourceBody423_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_82 sourceBody423_84

def sourceBody423_86 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 42)

def sourceBody423_87 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 34, Flapjack.WordLangExpHOL.const 8#64])
  22

def sourceBody423_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_87 sourceBody423_0

def sourceBody423_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_86 sourceBody423_88

def sourceBody423_90 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 14)

def sourceBody423_91 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 34, Flapjack.WordLangExpHOL.const 16#64])
  22

def sourceBody423_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_91 sourceBody423_0

def sourceBody423_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_90 sourceBody423_92

def sourceBody423_94 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 28)

def sourceBody423_95 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 34, Flapjack.WordLangExpHOL.const 24#64])
  22

def sourceBody423_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_95 sourceBody423_0

def sourceBody423_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_94 sourceBody423_96

def sourceBody423_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_97 sourceBody423_0

def sourceBody423_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_93 sourceBody423_98

def sourceBody423_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_89 sourceBody423_99

def sourceBody423_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_85 sourceBody423_100

def sourceBody423_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_81 sourceBody423_101

def sourceBody423_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_0 sourceBody423_102

def sourceBody423_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_80 sourceBody423_103

def sourceBody423_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_0 sourceBody423_104

def sourceBody423_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_79 sourceBody423_105

def sourceBody423_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_0 sourceBody423_106

def sourceBody423_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_78 sourceBody423_107

def sourceBody423_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_0 sourceBody423_108

def sourceBody423_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_77 sourceBody423_109

def sourceBody423_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_0 sourceBody423_110

def sourceBody423_112 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 2)

def sourceBody423_113 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 40)

def sourceBody423_114 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 26

def sourceBody423_115 : WordLangProgHOL (BitVec 64) :=
.call (some (([34]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody423_0, 423, 10)) (some 419) ([26, 42]) (some (26, sourceBody423_114, 423, 11))

def sourceBody423_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_115 sourceBody423_4

def sourceBody423_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_116 sourceBody423_0

def sourceBody423_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_113 sourceBody423_117

def sourceBody423_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_112 sourceBody423_118

def sourceBody423_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_0 sourceBody423_119

def sourceBody423_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_0 sourceBody423_120

def sourceBody423_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_111 sourceBody423_121

def sourceBody423_123 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 4)

def sourceBody423_124 : WordLangProgHOL (BitVec 64) :=
.call (some (([34]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody423_0, 423, 12)) (some 403) ([26]) (some (26, sourceBody423_114, 423, 13))

def sourceBody423_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_124 sourceBody423_4

def sourceBody423_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_125 sourceBody423_0

def sourceBody423_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_123 sourceBody423_126

def sourceBody423_128 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 34)

def sourceBody423_129 : WordLangProgHOL (BitVec 64) :=
.call (some (([34]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody423_0, 423, 14)) (some 391) ([26]) (some (26, sourceBody423_114, 423, 15))

def sourceBody423_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_129 sourceBody423_4

def sourceBody423_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_130 sourceBody423_0

def sourceBody423_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_128 sourceBody423_131

def sourceBody423_133 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 34, Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody423_134 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 34, Flapjack.WordLangExpHOL.const 8#64],
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody423_135 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 34, Flapjack.WordLangExpHOL.const 8#64],
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody423_136 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 34, Flapjack.WordLangExpHOL.const 8#64],
        Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody423_137 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 6)

def sourceBody423_138 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 8)

def sourceBody423_139 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 10)

def sourceBody423_140 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 12)

def sourceBody423_141 : WordLangProgHOL (BitVec 64) :=
.call (some (([30, 24, 38, 20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody423_0, 423, 16)) (some 116) ([26, 42, 14, 28, 22, 36, 18, 32]) (some (26, sourceBody423_114, 423, 17))

def sourceBody423_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_141 sourceBody423_4

def sourceBody423_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_142 sourceBody423_0

def sourceBody423_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_140 sourceBody423_143

def sourceBody423_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_139 sourceBody423_144

def sourceBody423_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_138 sourceBody423_145

def sourceBody423_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_137 sourceBody423_146

def sourceBody423_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_136 sourceBody423_147

def sourceBody423_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_135 sourceBody423_148

def sourceBody423_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_134 sourceBody423_149

def sourceBody423_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_133 sourceBody423_150

def sourceBody423_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_132 sourceBody423_151

def sourceBody423_153 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 34, Flapjack.WordLangExpHOL.const 8#64])

def sourceBody423_154 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 30)

def sourceBody423_155 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 24)

def sourceBody423_156 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 38)

def sourceBody423_157 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 20)

def sourceBody423_158 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 42)

def sourceBody423_159 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 26) 36

def sourceBody423_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_159 sourceBody423_0

def sourceBody423_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_158 sourceBody423_160

def sourceBody423_162 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 14)

def sourceBody423_163 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 26, Flapjack.WordLangExpHOL.const 8#64])
  36

def sourceBody423_164 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_163 sourceBody423_0

def sourceBody423_165 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_162 sourceBody423_164

def sourceBody423_166 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 28)

def sourceBody423_167 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 26, Flapjack.WordLangExpHOL.const 16#64])
  36

def sourceBody423_168 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_167 sourceBody423_0

def sourceBody423_169 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_166 sourceBody423_168

def sourceBody423_170 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 22)

def sourceBody423_171 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 26, Flapjack.WordLangExpHOL.const 24#64])
  36

def sourceBody423_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_171 sourceBody423_0

def sourceBody423_173 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_170 sourceBody423_172

def sourceBody423_174 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_173 sourceBody423_0

def sourceBody423_175 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_169 sourceBody423_174

def sourceBody423_176 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_165 sourceBody423_175

def sourceBody423_177 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_161 sourceBody423_176

def sourceBody423_178 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_157 sourceBody423_177

def sourceBody423_179 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_0 sourceBody423_178

def sourceBody423_180 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_156 sourceBody423_179

def sourceBody423_181 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_0 sourceBody423_180

def sourceBody423_182 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_155 sourceBody423_181

def sourceBody423_183 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_0 sourceBody423_182

def sourceBody423_184 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_154 sourceBody423_183

def sourceBody423_185 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_0 sourceBody423_184

def sourceBody423_186 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_153 sourceBody423_185

def sourceBody423_187 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_0 sourceBody423_186

def sourceBody423_188 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_152 sourceBody423_187

def sourceBody423_189 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 4)

def sourceBody423_190 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 34)

def sourceBody423_191 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 42

def sourceBody423_192 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody423_0, 423, 18)) (some 419) ([42, 14]) (some (42, sourceBody423_191, 423, 19))

def sourceBody423_193 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_192 sourceBody423_4

def sourceBody423_194 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_193 sourceBody423_0

def sourceBody423_195 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_190 sourceBody423_194

def sourceBody423_196 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_189 sourceBody423_195

def sourceBody423_197 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_0 sourceBody423_196

def sourceBody423_198 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_0 sourceBody423_197

def sourceBody423_199 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_188 sourceBody423_198

def sourceBody423_200 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody423_201 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [26]

def sourceBody423_202 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_201 sourceBody423_0

def sourceBody423_203 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_200 sourceBody423_202

def sourceBody423_204 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_199 sourceBody423_203

def sourceBody423_205 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_127 sourceBody423_204

def sourceBody423_206 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_0 sourceBody423_205

def sourceBody423_207 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_0 sourceBody423_206

def sourceBody423_208 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_122 sourceBody423_207

def sourceBody423_209 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_76 sourceBody423_208

def sourceBody423_210 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_0 sourceBody423_209

def sourceBody423_211 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_0 sourceBody423_210

def sourceBody423_212 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_0 sourceBody423_211

def sourceBody423_213 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_0 sourceBody423_212

def sourceBody423_214 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_0 sourceBody423_213

def sourceBody423_215 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_0 sourceBody423_214

def sourceBody423_216 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_0 sourceBody423_215

def sourceBody423_217 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_0 sourceBody423_216

def sourceBody423_218 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_56 sourceBody423_217

def sourceBody423_219 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_27 sourceBody423_218

def sourceBody423_220 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_0 sourceBody423_219

def sourceBody423_221 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_0 sourceBody423_220

def sourceBody423_222 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_7 sourceBody423_221

def sourceBody423_223 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_0 sourceBody423_222

def sourceBody423_224 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody423_0 sourceBody423_223

def source423 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (423, 7, sourceBody423_224)
end InitECandidate.Proofs.WordStages
