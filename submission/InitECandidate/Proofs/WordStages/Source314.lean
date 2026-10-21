import InitECandidate.Proofs.WordStages.Source298
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody314_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody314_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody314_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody314_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody314_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody314_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 28)

def sourceBody314_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody314_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody314_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody314_9 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 20 (Flapjack.WordRegImm.reg 14) sourceBody314_7 sourceBody314_8

def sourceBody314_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_9 sourceBody314_4

def sourceBody314_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 20)

def sourceBody314_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody314_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_12 sourceBody314_0

def sourceBody314_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_13 sourceBody314_0

def sourceBody314_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 2)

def sourceBody314_16 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 20 (Flapjack.WordRegImm.reg 14) sourceBody314_7 sourceBody314_8

def sourceBody314_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_16 sourceBody314_4

def sourceBody314_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_2 sourceBody314_0

def sourceBody314_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_18 sourceBody314_0

def sourceBody314_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 0#64]))

def sourceBody314_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 10)

def sourceBody314_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody314_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody314_24 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 14 (Flapjack.WordRegImm.reg 26) sourceBody314_23 sourceBody314_6

def sourceBody314_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_24 sourceBody314_4

def sourceBody314_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 14)

def sourceBody314_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 2#64)

def sourceBody314_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody314_29 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody314_0, 314, 2)) (some 282) ([14]) (some (14, sourceBody314_28, 314, 3))

def sourceBody314_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_29 sourceBody314_4

def sourceBody314_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_30 sourceBody314_0

def sourceBody314_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_27 sourceBody314_31

def sourceBody314_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_0 sourceBody314_32

def sourceBody314_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_0 sourceBody314_33

def sourceBody314_35 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.imm 0#64) sourceBody314_34 sourceBody314_0

def sourceBody314_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_35 sourceBody314_4

def sourceBody314_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_36 sourceBody314_0

def sourceBody314_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_26 sourceBody314_37

def sourceBody314_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_25 sourceBody314_38

def sourceBody314_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_22 sourceBody314_39

def sourceBody314_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_21 sourceBody314_40

def sourceBody314_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 2)

def sourceBody314_43 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody314_0, 314, 4)) (some 295) ([14]) (some (14, sourceBody314_28, 314, 5))

def sourceBody314_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_43 sourceBody314_4

def sourceBody314_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_44 sourceBody314_0

def sourceBody314_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_42 sourceBody314_45

def sourceBody314_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_0 sourceBody314_46

def sourceBody314_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_0 sourceBody314_47

def sourceBody314_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_41 sourceBody314_48

def sourceBody314_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody314_51 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 2)

def sourceBody314_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_51 sourceBody314_0

def sourceBody314_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_52 sourceBody314_0

def sourceBody314_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 40#64]))

def sourceBody314_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.var 8])

def sourceBody314_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 32#64]))

def sourceBody314_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.var 8])

def sourceBody314_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.var 8])

def sourceBody314_59 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody314_0, 314, 6)) (some 79) ([14, 26, 12]) (some (14, sourceBody314_28, 314, 7))

def sourceBody314_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_59 sourceBody314_4

def sourceBody314_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_60 sourceBody314_0

def sourceBody314_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_58 sourceBody314_61

def sourceBody314_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_57 sourceBody314_62

def sourceBody314_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_56 sourceBody314_63

def sourceBody314_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody314_66 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 26 (Flapjack.WordRegImm.reg 12) sourceBody314_50 sourceBody314_22

def sourceBody314_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_66 sourceBody314_4

def sourceBody314_68 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 26)

def sourceBody314_69 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 24 (Flapjack.WordRegImm.imm 0#64) sourceBody314_19 sourceBody314_0

def sourceBody314_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_69 sourceBody314_4

def sourceBody314_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_70 sourceBody314_0

def sourceBody314_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_68 sourceBody314_71

def sourceBody314_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_67 sourceBody314_72

def sourceBody314_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_65 sourceBody314_73

def sourceBody314_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_11 sourceBody314_74

def sourceBody314_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_64 sourceBody314_75

def sourceBody314_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_0 sourceBody314_76

def sourceBody314_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_0 sourceBody314_77

def sourceBody314_79 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.imm 0#64) sourceBody314_78 sourceBody314_0

def sourceBody314_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_79 sourceBody314_4

def sourceBody314_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_80 sourceBody314_0

def sourceBody314_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_26 sourceBody314_81

def sourceBody314_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_25 sourceBody314_82

def sourceBody314_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_55 sourceBody314_83

def sourceBody314_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_54 sourceBody314_84

def sourceBody314_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_53 sourceBody314_85

def sourceBody314_87 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 2#64)

def sourceBody314_88 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 32#64]))

def sourceBody314_89 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 20)

def sourceBody314_90 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 14)

def sourceBody314_91 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.var 8])

def sourceBody314_92 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.var 8])

def sourceBody314_93 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody314_94 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        Flapjack.Spt.ln)
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody314_0, 314, 8)) (some 287) ([12, 24, 18, 30]) (some (12, sourceBody314_93, 314, 9))

def sourceBody314_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_94 sourceBody314_4

def sourceBody314_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_95 sourceBody314_0

def sourceBody314_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_92 sourceBody314_96

def sourceBody314_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_91 sourceBody314_97

def sourceBody314_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_90 sourceBody314_98

def sourceBody314_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_89 sourceBody314_99

def sourceBody314_101 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 14)

def sourceBody314_102 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody314_103 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody314_104 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 24 (Flapjack.WordRegImm.reg 18) sourceBody314_102 sourceBody314_103

def sourceBody314_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_104 sourceBody314_4

def sourceBody314_106 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 24)

def sourceBody314_107 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 40#64)

def sourceBody314_108 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 24

def sourceBody314_109 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        Flapjack.Spt.ln)
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody314_0, 314, 10)) (some 74) ([24]) (some (24, sourceBody314_108, 314, 11))

def sourceBody314_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_109 sourceBody314_4

def sourceBody314_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_110 sourceBody314_0

def sourceBody314_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_107 sourceBody314_111

def sourceBody314_113 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 0#64])

def sourceBody314_114 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 22)

def sourceBody314_115 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 18)

def sourceBody314_116 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 24) 30

def sourceBody314_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_116 sourceBody314_0

def sourceBody314_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_115 sourceBody314_117

def sourceBody314_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_118 sourceBody314_0

def sourceBody314_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_114 sourceBody314_119

def sourceBody314_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_0 sourceBody314_120

def sourceBody314_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_113 sourceBody314_121

def sourceBody314_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_0 sourceBody314_122

def sourceBody314_124 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 8#64])

def sourceBody314_125 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 2)

def sourceBody314_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_125 sourceBody314_119

def sourceBody314_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_0 sourceBody314_126

def sourceBody314_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_124 sourceBody314_127

def sourceBody314_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_0 sourceBody314_128

def sourceBody314_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_123 sourceBody314_129

def sourceBody314_131 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 16#64])

def sourceBody314_132 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 2#64)

def sourceBody314_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_132 sourceBody314_119

def sourceBody314_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_0 sourceBody314_133

def sourceBody314_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_131 sourceBody314_134

def sourceBody314_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_0 sourceBody314_135

def sourceBody314_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_130 sourceBody314_136

def sourceBody314_138 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 24#64])

def sourceBody314_139 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 20)

def sourceBody314_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_139 sourceBody314_119

def sourceBody314_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_0 sourceBody314_140

def sourceBody314_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_138 sourceBody314_141

def sourceBody314_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_0 sourceBody314_142

def sourceBody314_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_137 sourceBody314_143

def sourceBody314_145 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 32#64])

def sourceBody314_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_101 sourceBody314_119

def sourceBody314_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_0 sourceBody314_146

def sourceBody314_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_145 sourceBody314_147

def sourceBody314_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_0 sourceBody314_148

def sourceBody314_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_144 sourceBody314_149

def sourceBody314_151 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 12)

def sourceBody314_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_151 sourceBody314_0

def sourceBody314_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_152 sourceBody314_0

def sourceBody314_154 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_150 sourceBody314_153

def sourceBody314_155 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 48#64]))

def sourceBody314_156 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 24)

def sourceBody314_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_156 sourceBody314_0

def sourceBody314_158 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_157 sourceBody314_0

def sourceBody314_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_155 sourceBody314_158

def sourceBody314_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_0 sourceBody314_159

def sourceBody314_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_154 sourceBody314_160

def sourceBody314_162 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.var 14])

def sourceBody314_163 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 24)

def sourceBody314_164 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_163 sourceBody314_0

def sourceBody314_165 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_164 sourceBody314_0

def sourceBody314_166 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_162 sourceBody314_165

def sourceBody314_167 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_0 sourceBody314_166

def sourceBody314_168 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_161 sourceBody314_167

def sourceBody314_169 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_3 sourceBody314_0

def sourceBody314_170 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_169 sourceBody314_0

def sourceBody314_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_168 sourceBody314_170

def sourceBody314_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_112 sourceBody314_171

def sourceBody314_173 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_0 sourceBody314_172

def sourceBody314_174 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_0 sourceBody314_173

def sourceBody314_175 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 30 (Flapjack.WordRegImm.imm 0#64) sourceBody314_53 sourceBody314_174

def sourceBody314_176 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_175 sourceBody314_4

def sourceBody314_177 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_176 sourceBody314_0

def sourceBody314_178 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_106 sourceBody314_177

def sourceBody314_179 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_105 sourceBody314_178

def sourceBody314_180 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_101 sourceBody314_179

def sourceBody314_181 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_68 sourceBody314_180

def sourceBody314_182 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_100 sourceBody314_181

def sourceBody314_183 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_0 sourceBody314_182

def sourceBody314_184 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_0 sourceBody314_183

def sourceBody314_185 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_54 sourceBody314_184

def sourceBody314_186 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_0 sourceBody314_185

def sourceBody314_187 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_88 sourceBody314_186

def sourceBody314_188 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_0 sourceBody314_187

def sourceBody314_189 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 8)

def sourceBody314_190 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 6)

def sourceBody314_191 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 168#64]))

def sourceBody314_192 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 160#64])

def sourceBody314_193 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 14)

def sourceBody314_194 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 20) 26

def sourceBody314_195 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_194 sourceBody314_0

def sourceBody314_196 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_193 sourceBody314_195

def sourceBody314_197 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_196 sourceBody314_0

def sourceBody314_198 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_6 sourceBody314_197

def sourceBody314_199 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_0 sourceBody314_198

def sourceBody314_200 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_192 sourceBody314_199

def sourceBody314_201 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_0 sourceBody314_200

def sourceBody314_202 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 168#64])

def sourceBody314_203 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_202 sourceBody314_199

def sourceBody314_204 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_0 sourceBody314_203

def sourceBody314_205 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_201 sourceBody314_204

def sourceBody314_206 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody314_207 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody314_0, 314, 12)) (some 312) ([20]) (some (20, sourceBody314_206, 314, 13))

def sourceBody314_208 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_207 sourceBody314_4

def sourceBody314_209 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_208 sourceBody314_0

def sourceBody314_210 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_15 sourceBody314_209

def sourceBody314_211 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_205 sourceBody314_210

def sourceBody314_212 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.imm 0#64) sourceBody314_53 sourceBody314_211

def sourceBody314_213 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_212 sourceBody314_4

def sourceBody314_214 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_213 sourceBody314_0

def sourceBody314_215 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_26 sourceBody314_214

def sourceBody314_216 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_25 sourceBody314_215

def sourceBody314_217 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_22 sourceBody314_216

def sourceBody314_218 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_191 sourceBody314_217

def sourceBody314_219 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.var 8])

def sourceBody314_220 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 20 (Flapjack.WordLangAddr.addr 20 0#64))

def sourceBody314_221 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_220 sourceBody314_0

def sourceBody314_222 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_219 sourceBody314_221

def sourceBody314_223 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 20)

def sourceBody314_224 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 40#64)

def sourceBody314_225 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        Flapjack.Spt.ln)
      PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody314_0, 314, 14)) (some 74) ([12]) (some (12, sourceBody314_93, 314, 15))

def sourceBody314_226 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_225 sourceBody314_4

def sourceBody314_227 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_226 sourceBody314_0

def sourceBody314_228 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_224 sourceBody314_227

def sourceBody314_229 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 26, Flapjack.WordLangExpHOL.const 0#64])

def sourceBody314_230 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 22)

def sourceBody314_231 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 24)

def sourceBody314_232 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 12) 18

def sourceBody314_233 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_232 sourceBody314_0

def sourceBody314_234 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_231 sourceBody314_233

def sourceBody314_235 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_234 sourceBody314_0

def sourceBody314_236 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_230 sourceBody314_235

def sourceBody314_237 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_0 sourceBody314_236

def sourceBody314_238 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_229 sourceBody314_237

def sourceBody314_239 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_0 sourceBody314_238

def sourceBody314_240 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 26, Flapjack.WordLangExpHOL.const 8#64])

def sourceBody314_241 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 2)

def sourceBody314_242 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_241 sourceBody314_235

def sourceBody314_243 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_0 sourceBody314_242

def sourceBody314_244 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_240 sourceBody314_243

def sourceBody314_245 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_0 sourceBody314_244

def sourceBody314_246 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_239 sourceBody314_245

def sourceBody314_247 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 26, Flapjack.WordLangExpHOL.const 16#64])

def sourceBody314_248 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 3#64)

def sourceBody314_249 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_248 sourceBody314_235

def sourceBody314_250 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_0 sourceBody314_249

def sourceBody314_251 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_247 sourceBody314_250

def sourceBody314_252 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_0 sourceBody314_251

def sourceBody314_253 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_246 sourceBody314_252

def sourceBody314_254 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 26, Flapjack.WordLangExpHOL.const 32#64])

def sourceBody314_255 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_90 sourceBody314_235

def sourceBody314_256 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_0 sourceBody314_255

def sourceBody314_257 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_254 sourceBody314_256

def sourceBody314_258 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_0 sourceBody314_257

def sourceBody314_259 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_253 sourceBody314_258

def sourceBody314_260 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 26)

def sourceBody314_261 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_260 sourceBody314_0

def sourceBody314_262 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_261 sourceBody314_0

def sourceBody314_263 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_259 sourceBody314_262

def sourceBody314_264 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 32#64,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 14)
          (Flapjack.WordLangExpHOL.const 3#64)]))

def sourceBody314_265 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 12)

def sourceBody314_266 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_265 sourceBody314_0

def sourceBody314_267 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_266 sourceBody314_0

def sourceBody314_268 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_264 sourceBody314_267

def sourceBody314_269 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_0 sourceBody314_268

def sourceBody314_270 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_263 sourceBody314_269

def sourceBody314_271 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody314_272 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 12)

def sourceBody314_273 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_272 sourceBody314_0

def sourceBody314_274 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_273 sourceBody314_0

def sourceBody314_275 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_271 sourceBody314_274

def sourceBody314_276 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_0 sourceBody314_275

def sourceBody314_277 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_270 sourceBody314_276

def sourceBody314_278 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_277 sourceBody314_170

def sourceBody314_279 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_228 sourceBody314_278

def sourceBody314_280 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_0 sourceBody314_279

def sourceBody314_281 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_0 sourceBody314_280

def sourceBody314_282 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_223 sourceBody314_281

def sourceBody314_283 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_222 sourceBody314_282

def sourceBody314_284 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.imm 0#64) sourceBody314_218 sourceBody314_283

def sourceBody314_285 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_284 sourceBody314_4

def sourceBody314_286 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_285 sourceBody314_0

def sourceBody314_287 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_26 sourceBody314_286

def sourceBody314_288 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_25 sourceBody314_287

def sourceBody314_289 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_190 sourceBody314_288

def sourceBody314_290 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_189 sourceBody314_289

def sourceBody314_291 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.imm 0#64) sourceBody314_188 sourceBody314_290

def sourceBody314_292 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_291 sourceBody314_4

def sourceBody314_293 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_292 sourceBody314_0

def sourceBody314_294 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_26 sourceBody314_293

def sourceBody314_295 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_25 sourceBody314_294

def sourceBody314_296 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_87 sourceBody314_295

def sourceBody314_297 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_21 sourceBody314_296

def sourceBody314_298 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.imm 0#64) sourceBody314_86 sourceBody314_297

def sourceBody314_299 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_298 sourceBody314_4

def sourceBody314_300 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_299 sourceBody314_0

def sourceBody314_301 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_26 sourceBody314_300

def sourceBody314_302 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_25 sourceBody314_301

def sourceBody314_303 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_50 sourceBody314_302

def sourceBody314_304 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_21 sourceBody314_303

def sourceBody314_305 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_49 sourceBody314_304

def sourceBody314_306 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_20 sourceBody314_305

def sourceBody314_307 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_0 sourceBody314_306

def sourceBody314_308 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 26 (Flapjack.WordRegImm.imm 0#64) sourceBody314_19 sourceBody314_307

def sourceBody314_309 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_308 sourceBody314_4

def sourceBody314_310 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_309 sourceBody314_0

def sourceBody314_311 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_11 sourceBody314_310

def sourceBody314_312 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_17 sourceBody314_311

def sourceBody314_313 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_6 sourceBody314_312

def sourceBody314_314 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_15 sourceBody314_313

def sourceBody314_315 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_14 sourceBody314_314

def sourceBody314_316 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody314_317 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_315 sourceBody314_316

def sourceBody314_318 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody314_319 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 26 (Flapjack.WordRegImm.imm 0#64) sourceBody314_317 sourceBody314_318

def sourceBody314_320 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_319 sourceBody314_4

def sourceBody314_321 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_320 sourceBody314_0

def sourceBody314_322 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_11 sourceBody314_321

def sourceBody314_323 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_10 sourceBody314_322

def sourceBody314_324 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_6 sourceBody314_323

def sourceBody314_325 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_5 sourceBody314_324

def sourceBody314_326 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)
    PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
  PUnit.unit Flapjack.Spt.ln) sourceBody314_325 (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)
    PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody314_327 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_326 sourceBody314_4

def sourceBody314_328 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_4 sourceBody314_327

def sourceBody314_329 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 22)

def sourceBody314_330 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 22, Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody314_331 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 22, Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody314_332 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 10)

def sourceBody314_333 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 22, Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody314_334 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 22, Flapjack.WordLangExpHOL.const 32#64]))

def sourceBody314_335 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 16)

def sourceBody314_336 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody314_0, 314, 16)) (some 313) ([20, 14, 26, 12]) (some (20, sourceBody314_206, 314, 17))

def sourceBody314_337 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_336 sourceBody314_4

def sourceBody314_338 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_337 sourceBody314_0

def sourceBody314_339 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_335 sourceBody314_338

def sourceBody314_340 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_334 sourceBody314_339

def sourceBody314_341 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_333 sourceBody314_340

def sourceBody314_342 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_332 sourceBody314_341

def sourceBody314_343 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 32#64,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
        (Flapjack.WordLangExpHOL.load
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
            [Flapjack.WordLangExpHOL.var 22, Flapjack.WordLangExpHOL.const 32#64]))
        (Flapjack.WordLangExpHOL.const 3#64)])

def sourceBody314_344 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 16)

def sourceBody314_345 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_344 sourceBody314_197

def sourceBody314_346 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_0 sourceBody314_345

def sourceBody314_347 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_343 sourceBody314_346

def sourceBody314_348 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_0 sourceBody314_347

def sourceBody314_349 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody314_0, 314, 18)) (some 312) ([20]) (some (20, sourceBody314_206, 314, 19))

def sourceBody314_350 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_349 sourceBody314_4

def sourceBody314_351 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_350 sourceBody314_0

def sourceBody314_352 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_332 sourceBody314_351

def sourceBody314_353 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_348 sourceBody314_352

def sourceBody314_354 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.imm 0#64) sourceBody314_342 sourceBody314_353

def sourceBody314_355 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_354 sourceBody314_4

def sourceBody314_356 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_355 sourceBody314_0

def sourceBody314_357 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_26 sourceBody314_356

def sourceBody314_358 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_25 sourceBody314_357

def sourceBody314_359 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_87 sourceBody314_358

def sourceBody314_360 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_331 sourceBody314_359

def sourceBody314_361 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 22, Flapjack.WordLangExpHOL.const 0#64]))

def sourceBody314_362 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 20)

def sourceBody314_363 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_362 sourceBody314_0

def sourceBody314_364 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_363 sourceBody314_0

def sourceBody314_365 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_361 sourceBody314_364

def sourceBody314_366 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_0 sourceBody314_365

def sourceBody314_367 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_360 sourceBody314_366

def sourceBody314_368 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_330 sourceBody314_367

def sourceBody314_369 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_0 sourceBody314_368

def sourceBody314_370 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_369 sourceBody314_316

def sourceBody314_371 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 26 (Flapjack.WordRegImm.imm 0#64) sourceBody314_370 sourceBody314_318

def sourceBody314_372 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_371 sourceBody314_4

def sourceBody314_373 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_372 sourceBody314_0

def sourceBody314_374 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_11 sourceBody314_373

def sourceBody314_375 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_10 sourceBody314_374

def sourceBody314_376 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_6 sourceBody314_375

def sourceBody314_377 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_329 sourceBody314_376

def sourceBody314_378 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)
    PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
  PUnit.unit Flapjack.Spt.ln) sourceBody314_377 (Flapjack.Spt.bs
  (Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody314_379 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_378 sourceBody314_4

def sourceBody314_380 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_4 sourceBody314_379

def sourceBody314_381 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_328 sourceBody314_380

def sourceBody314_382 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 16)

def sourceBody314_383 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [10]

def sourceBody314_384 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_383 sourceBody314_0

def sourceBody314_385 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_382 sourceBody314_384

def sourceBody314_386 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_381 sourceBody314_385

def sourceBody314_387 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_3 sourceBody314_386

def sourceBody314_388 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_0 sourceBody314_387

def sourceBody314_389 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_2 sourceBody314_388

def sourceBody314_390 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_0 sourceBody314_389

def sourceBody314_391 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_1 sourceBody314_390

def sourceBody314_392 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody314_0 sourceBody314_391

def source314 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (314, 5, sourceBody314_392)
end InitECandidate.Proofs.WordStages
