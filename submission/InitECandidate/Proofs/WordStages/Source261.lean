import InitECandidate.Proofs.WordStages.Source245
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody261_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody261_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 28

def sourceBody261_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody261_0, 261, 2)) (some 69) ([]) (some (28, sourceBody261_1, 261, 3))

def sourceBody261_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody261_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_2 sourceBody261_3

def sourceBody261_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_4 sourceBody261_0

def sourceBody261_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 6)
        (Flapjack.WordLangExpHOL.const 5#64),
      Flapjack.WordLangExpHOL.const 32#64])

def sourceBody261_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody261_8 : WordLangProgHOL (BitVec 64) :=
.call (some (([28]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody261_0, 261, 4)) (some 68) ([12]) (some (12, sourceBody261_7, 261, 5))

def sourceBody261_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_8 sourceBody261_3

def sourceBody261_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_9 sourceBody261_0

def sourceBody261_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_6 sourceBody261_10

def sourceBody261_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody261_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 12)

def sourceBody261_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 6)

def sourceBody261_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody261_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody261_17 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.less) 16 (Flapjack.WordRegImm.reg 26) sourceBody261_15 sourceBody261_16

def sourceBody261_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_17 sourceBody261_3

def sourceBody261_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 16)

def sourceBody261_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 2)

def sourceBody261_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody261_22 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 16 (Flapjack.WordRegImm.reg 26) sourceBody261_15 sourceBody261_16

def sourceBody261_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_22 sourceBody261_3

def sourceBody261_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 8)

def sourceBody261_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.longMul 14 14 16 26))

def sourceBody261_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.var 14])

def sourceBody261_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 28,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 12)
        (Flapjack.WordLangExpHOL.const 5#64)])

def sourceBody261_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody261_29 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody261_0, 261, 6)) (some 256) ([24, 20]) (some (16, sourceBody261_28, 261, 7))

def sourceBody261_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_29 sourceBody261_3

def sourceBody261_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_30 sourceBody261_0

def sourceBody261_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_27 sourceBody261_31

def sourceBody261_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_26 sourceBody261_32

def sourceBody261_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_25 sourceBody261_33

def sourceBody261_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_24 sourceBody261_34

def sourceBody261_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_13 sourceBody261_35

def sourceBody261_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_0 sourceBody261_36

def sourceBody261_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_0 sourceBody261_37

def sourceBody261_39 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.WordRegImm.imm 0#64) sourceBody261_38 sourceBody261_0

def sourceBody261_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_39 sourceBody261_3

def sourceBody261_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_40 sourceBody261_0

def sourceBody261_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_19 sourceBody261_41

def sourceBody261_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_23 sourceBody261_42

def sourceBody261_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_21 sourceBody261_43

def sourceBody261_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_20 sourceBody261_44

def sourceBody261_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody261_47 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody261_0, 261, 8)) (some 257) ([24, 20]) (some (16, sourceBody261_28, 261, 9))

def sourceBody261_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_47 sourceBody261_3

def sourceBody261_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_48 sourceBody261_0

def sourceBody261_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_27 sourceBody261_49

def sourceBody261_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_26 sourceBody261_50

def sourceBody261_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_25 sourceBody261_51

def sourceBody261_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_24 sourceBody261_52

def sourceBody261_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_13 sourceBody261_53

def sourceBody261_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_0 sourceBody261_54

def sourceBody261_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_0 sourceBody261_55

def sourceBody261_57 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.WordRegImm.imm 0#64) sourceBody261_56 sourceBody261_0

def sourceBody261_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_57 sourceBody261_3

def sourceBody261_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_58 sourceBody261_0

def sourceBody261_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_19 sourceBody261_59

def sourceBody261_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_23 sourceBody261_60

def sourceBody261_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_46 sourceBody261_61

def sourceBody261_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_20 sourceBody261_62

def sourceBody261_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_45 sourceBody261_63

def sourceBody261_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 2#64)

def sourceBody261_66 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody261_0, 261, 10)) (some 258) ([24, 20]) (some (16, sourceBody261_28, 261, 11))

def sourceBody261_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_66 sourceBody261_3

def sourceBody261_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_67 sourceBody261_0

def sourceBody261_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_27 sourceBody261_68

def sourceBody261_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_26 sourceBody261_69

def sourceBody261_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_25 sourceBody261_70

def sourceBody261_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_24 sourceBody261_71

def sourceBody261_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_13 sourceBody261_72

def sourceBody261_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_0 sourceBody261_73

def sourceBody261_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_0 sourceBody261_74

def sourceBody261_76 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.WordRegImm.imm 0#64) sourceBody261_75 sourceBody261_0

def sourceBody261_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_76 sourceBody261_3

def sourceBody261_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_77 sourceBody261_0

def sourceBody261_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_19 sourceBody261_78

def sourceBody261_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_23 sourceBody261_79

def sourceBody261_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_65 sourceBody261_80

def sourceBody261_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_20 sourceBody261_81

def sourceBody261_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_64 sourceBody261_82

def sourceBody261_84 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 3#64)

def sourceBody261_85 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody261_0, 261, 12)) (some 259) ([24, 20]) (some (16, sourceBody261_28, 261, 13))

def sourceBody261_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_85 sourceBody261_3

def sourceBody261_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_86 sourceBody261_0

def sourceBody261_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_27 sourceBody261_87

def sourceBody261_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_26 sourceBody261_88

def sourceBody261_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_25 sourceBody261_89

def sourceBody261_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_24 sourceBody261_90

def sourceBody261_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_13 sourceBody261_91

def sourceBody261_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_0 sourceBody261_92

def sourceBody261_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_0 sourceBody261_93

def sourceBody261_95 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.WordRegImm.imm 0#64) sourceBody261_94 sourceBody261_0

def sourceBody261_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_95 sourceBody261_3

def sourceBody261_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_96 sourceBody261_0

def sourceBody261_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_19 sourceBody261_97

def sourceBody261_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_23 sourceBody261_98

def sourceBody261_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_84 sourceBody261_99

def sourceBody261_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_20 sourceBody261_100

def sourceBody261_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_83 sourceBody261_101

def sourceBody261_103 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 4#64)

def sourceBody261_104 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody261_0, 261, 14)) (some 260) ([24, 20]) (some (16, sourceBody261_28, 261, 15))

def sourceBody261_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_104 sourceBody261_3

def sourceBody261_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_105 sourceBody261_0

def sourceBody261_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_27 sourceBody261_106

def sourceBody261_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_26 sourceBody261_107

def sourceBody261_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_25 sourceBody261_108

def sourceBody261_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_24 sourceBody261_109

def sourceBody261_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_13 sourceBody261_110

def sourceBody261_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_0 sourceBody261_111

def sourceBody261_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_0 sourceBody261_112

def sourceBody261_114 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.WordRegImm.imm 0#64) sourceBody261_113 sourceBody261_0

def sourceBody261_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_114 sourceBody261_3

def sourceBody261_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_115 sourceBody261_0

def sourceBody261_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_19 sourceBody261_116

def sourceBody261_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_23 sourceBody261_117

def sourceBody261_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_103 sourceBody261_118

def sourceBody261_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_20 sourceBody261_119

def sourceBody261_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_102 sourceBody261_120

def sourceBody261_122 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody261_123 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 22)

def sourceBody261_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_123 sourceBody261_0

def sourceBody261_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_124 sourceBody261_0

def sourceBody261_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_122 sourceBody261_125

def sourceBody261_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_0 sourceBody261_126

def sourceBody261_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_121 sourceBody261_127

def sourceBody261_129 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody261_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_128 sourceBody261_129

def sourceBody261_131 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody261_132 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.WordRegImm.imm 0#64) sourceBody261_130 sourceBody261_131

def sourceBody261_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_132 sourceBody261_3

def sourceBody261_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_133 sourceBody261_0

def sourceBody261_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_19 sourceBody261_134

def sourceBody261_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_18 sourceBody261_135

def sourceBody261_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_14 sourceBody261_136

def sourceBody261_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_13 sourceBody261_137

def sourceBody261_139 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
      (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit Flapjack.Spt.ln) sourceBody261_138 (Flapjack.Spt.bs
  (Flapjack.Spt.bn
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody261_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_139 sourceBody261_3

def sourceBody261_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_3 sourceBody261_140

def sourceBody261_142 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 28)

def sourceBody261_143 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 6)

def sourceBody261_144 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 10)

def sourceBody261_145 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody261_0, 261, 16)) (some 238) ([16, 26, 14, 24]) (some (16, sourceBody261_28, 261, 17))

def sourceBody261_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_145 sourceBody261_3

def sourceBody261_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_146 sourceBody261_0

def sourceBody261_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_144 sourceBody261_147

def sourceBody261_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_143 sourceBody261_148

def sourceBody261_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_14 sourceBody261_149

def sourceBody261_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_142 sourceBody261_150

def sourceBody261_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_0 sourceBody261_151

def sourceBody261_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_0 sourceBody261_152

def sourceBody261_154 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_141 sourceBody261_153

def sourceBody261_155 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 18)

def sourceBody261_156 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody261_0, 261, 18)) (some 70) ([16]) (some (16, sourceBody261_28, 261, 19))

def sourceBody261_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_156 sourceBody261_3

def sourceBody261_158 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_157 sourceBody261_0

def sourceBody261_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_155 sourceBody261_158

def sourceBody261_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_0 sourceBody261_159

def sourceBody261_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_0 sourceBody261_160

def sourceBody261_162 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_154 sourceBody261_161

def sourceBody261_163 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody261_164 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [22]

def sourceBody261_165 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_164 sourceBody261_0

def sourceBody261_166 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_163 sourceBody261_165

def sourceBody261_167 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_162 sourceBody261_166

def sourceBody261_168 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_12 sourceBody261_167

def sourceBody261_169 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_0 sourceBody261_168

def sourceBody261_170 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_11 sourceBody261_169

def sourceBody261_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_0 sourceBody261_170

def sourceBody261_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_0 sourceBody261_171

def sourceBody261_173 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_5 sourceBody261_172

def sourceBody261_174 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_0 sourceBody261_173

def sourceBody261_175 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody261_0 sourceBody261_174

def source261 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (261, 6, sourceBody261_175)
end InitECandidate.Proofs.WordStages
