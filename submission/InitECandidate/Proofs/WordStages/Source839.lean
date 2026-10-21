import InitECandidate.Proofs.WordStages.Source823
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody839_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody839_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 8)

def sourceBody839_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody839_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody839_0, 839, 2)) (some 837) ([16]) (some (16, sourceBody839_2, 839, 3))

def sourceBody839_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody839_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_3 sourceBody839_4

def sourceBody839_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_5 sourceBody839_0

def sourceBody839_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_1 sourceBody839_6

def sourceBody839_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 22, Flapjack.WordLangExpHOL.const 400#64])

def sourceBody839_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 28

def sourceBody839_10 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody839_0, 839, 4)) (some 68) ([28]) (some (28, sourceBody839_9, 839, 5))

def sourceBody839_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_10 sourceBody839_4

def sourceBody839_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_11 sourceBody839_0

def sourceBody839_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_8 sourceBody839_12

def sourceBody839_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 16, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody839_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 28, Flapjack.WordLangExpHOL.const 9#64])

def sourceBody839_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 4)

def sourceBody839_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody839_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody839_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody839_20 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 26 (Flapjack.WordRegImm.reg 12) sourceBody839_18 sourceBody839_19

def sourceBody839_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_20 sourceBody839_4

def sourceBody839_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 26)

def sourceBody839_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 10)

def sourceBody839_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.store8 26 (Flapjack.WordLangAddr.addr 14 0#64))

def sourceBody839_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_24 sourceBody839_0

def sourceBody839_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_18 sourceBody839_25

def sourceBody839_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_23 sourceBody839_26

def sourceBody839_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody839_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_28 sourceBody839_0

def sourceBody839_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_29 sourceBody839_0

def sourceBody839_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_27 sourceBody839_30

def sourceBody839_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 128#64)

def sourceBody839_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_32 sourceBody839_25

def sourceBody839_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_23 sourceBody839_33

def sourceBody839_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_34 sourceBody839_30

def sourceBody839_36 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 24 (Flapjack.WordRegImm.imm 0#64) sourceBody839_31 sourceBody839_35

def sourceBody839_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_36 sourceBody839_4

def sourceBody839_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_37 sourceBody839_0

def sourceBody839_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_22 sourceBody839_38

def sourceBody839_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_21 sourceBody839_39

def sourceBody839_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_17 sourceBody839_40

def sourceBody839_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_16 sourceBody839_41

def sourceBody839_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.var 20])

def sourceBody839_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 14)

def sourceBody839_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_44 sourceBody839_0

def sourceBody839_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_45 sourceBody839_0

def sourceBody839_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_43 sourceBody839_46

def sourceBody839_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_0 sourceBody839_47

def sourceBody839_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_42 sourceBody839_48

def sourceBody839_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 6)

def sourceBody839_51 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody839_52 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody839_0, 839, 6)) (some 177) ([14, 26]) (some (14, sourceBody839_51, 839, 7))

def sourceBody839_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_52 sourceBody839_4

def sourceBody839_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_53 sourceBody839_0

def sourceBody839_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_50 sourceBody839_54

def sourceBody839_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_23 sourceBody839_55

def sourceBody839_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_49 sourceBody839_56

def sourceBody839_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_57 sourceBody839_48

def sourceBody839_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 256#64)

def sourceBody839_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 26

def sourceBody839_61 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody839_0, 839, 8)) (some 68) ([26]) (some (26, sourceBody839_60, 839, 9))

def sourceBody839_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_61 sourceBody839_4

def sourceBody839_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_62 sourceBody839_0

def sourceBody839_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_59 sourceBody839_63

def sourceBody839_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 8)

def sourceBody839_66 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 14)

def sourceBody839_67 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody839_68 : WordLangProgHOL (BitVec 64) :=
.call (some (([26]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody839_0, 839, 10)) (some 835) ([12, 24]) (some (12, sourceBody839_67, 839, 11))

def sourceBody839_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_68 sourceBody839_4

def sourceBody839_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_69 sourceBody839_0

def sourceBody839_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_66 sourceBody839_70

def sourceBody839_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_65 sourceBody839_71

def sourceBody839_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_0 sourceBody839_72

def sourceBody839_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_0 sourceBody839_73

def sourceBody839_75 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 10)

def sourceBody839_76 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 14)

def sourceBody839_77 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 256#64)

def sourceBody839_78 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody839_0, 839, 12)) (some 176) ([26, 12, 24]) (some (26, sourceBody839_60, 839, 13))

def sourceBody839_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_78 sourceBody839_4

def sourceBody839_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_79 sourceBody839_0

def sourceBody839_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_77 sourceBody839_80

def sourceBody839_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_76 sourceBody839_81

def sourceBody839_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_75 sourceBody839_82

def sourceBody839_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_74 sourceBody839_83

def sourceBody839_85 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.var 20])

def sourceBody839_86 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 26)

def sourceBody839_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_86 sourceBody839_0

def sourceBody839_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_87 sourceBody839_0

def sourceBody839_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_85 sourceBody839_88

def sourceBody839_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_0 sourceBody839_89

def sourceBody839_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_84 sourceBody839_90

def sourceBody839_92 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody839_0, 839, 14)) (some 838) ([26, 12]) (some (26, sourceBody839_60, 839, 15))

def sourceBody839_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_92 sourceBody839_4

def sourceBody839_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_93 sourceBody839_0

def sourceBody839_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_65 sourceBody839_94

def sourceBody839_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_75 sourceBody839_95

def sourceBody839_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_91 sourceBody839_96

def sourceBody839_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_97 sourceBody839_90

def sourceBody839_99 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 28)

def sourceBody839_100 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 10)

def sourceBody839_101 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody839_0, 839, 16)) (some 836) ([26, 12]) (some (26, sourceBody839_60, 839, 17))

def sourceBody839_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_101 sourceBody839_4

def sourceBody839_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_102 sourceBody839_0

def sourceBody839_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_100 sourceBody839_103

def sourceBody839_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_99 sourceBody839_104

def sourceBody839_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_98 sourceBody839_105

def sourceBody839_107 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 2)

def sourceBody839_108 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody839_109 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody839_110 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.reg 24) sourceBody839_109 sourceBody839_17

def sourceBody839_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_110 sourceBody839_4

def sourceBody839_112 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 12)

def sourceBody839_113 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 28, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody839_114 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.store8 12 (Flapjack.WordLangAddr.addr 26 0#64))

def sourceBody839_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_114 sourceBody839_0

def sourceBody839_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_107 sourceBody839_115

def sourceBody839_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_113 sourceBody839_116

def sourceBody839_118 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 20, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody839_119 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [26, 12]

def sourceBody839_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_119 sourceBody839_0

def sourceBody839_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_118 sourceBody839_120

def sourceBody839_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_113 sourceBody839_121

def sourceBody839_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_117 sourceBody839_122

def sourceBody839_124 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 18 (Flapjack.WordRegImm.imm 0#64) sourceBody839_123 sourceBody839_0

def sourceBody839_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_124 sourceBody839_4

def sourceBody839_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_125 sourceBody839_0

def sourceBody839_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_112 sourceBody839_126

def sourceBody839_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_111 sourceBody839_127

def sourceBody839_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_108 sourceBody839_128

def sourceBody839_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_107 sourceBody839_129

def sourceBody839_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_106 sourceBody839_130

def sourceBody839_132 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 20)

def sourceBody839_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_132 sourceBody839_120

def sourceBody839_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_99 sourceBody839_133

def sourceBody839_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_131 sourceBody839_134

def sourceBody839_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_64 sourceBody839_135

def sourceBody839_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_0 sourceBody839_136

def sourceBody839_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_0 sourceBody839_137

def sourceBody839_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_58 sourceBody839_138

def sourceBody839_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_0 sourceBody839_139

def sourceBody839_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_0 sourceBody839_140

def sourceBody839_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_15 sourceBody839_141

def sourceBody839_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_0 sourceBody839_142

def sourceBody839_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_14 sourceBody839_143

def sourceBody839_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_0 sourceBody839_144

def sourceBody839_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_13 sourceBody839_145

def sourceBody839_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_0 sourceBody839_146

def sourceBody839_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_0 sourceBody839_147

def sourceBody839_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_7 sourceBody839_148

def sourceBody839_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_0 sourceBody839_149

def sourceBody839_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody839_0 sourceBody839_150

def source839 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (839, 5, sourceBody839_151)
end InitECandidate.Proofs.WordStages
