import InitECandidate.Proofs.WordStages.Source230
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody246_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 4)

def sourceBody246_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody246_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody246_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody246_4 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 18 (Flapjack.WordRegImm.reg 28) sourceBody246_2 sourceBody246_3

def sourceBody246_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody246_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody246_4 sourceBody246_5

def sourceBody246_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 18)

def sourceBody246_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody246_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [24]

def sourceBody246_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody246_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody246_9 sourceBody246_10

def sourceBody246_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody246_8 sourceBody246_11

def sourceBody246_13 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.imm 0#64) sourceBody246_12 sourceBody246_10

def sourceBody246_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody246_13 sourceBody246_5

def sourceBody246_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody246_14 sourceBody246_10

def sourceBody246_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody246_7 sourceBody246_15

def sourceBody246_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody246_6 sourceBody246_16

def sourceBody246_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody246_1 sourceBody246_17

def sourceBody246_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody246_0 sourceBody246_18

def sourceBody246_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 24)

def sourceBody246_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 4)

def sourceBody246_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody246_23 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.less) 28 (Flapjack.WordRegImm.reg 12) sourceBody246_22 sourceBody246_1

def sourceBody246_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody246_23 sourceBody246_5

def sourceBody246_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 28)

def sourceBody246_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 24)
          (Flapjack.WordLangExpHOL.const 3#64)]))

def sourceBody246_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 6)

def sourceBody246_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody246_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody246_30 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 12 (Flapjack.WordRegImm.reg 22) sourceBody246_28 sourceBody246_29

def sourceBody246_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody246_30 sourceBody246_5

def sourceBody246_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 8)

def sourceBody246_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 18)

def sourceBody246_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody246_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody246_36 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 26 (Flapjack.WordRegImm.reg 14) sourceBody246_34 sourceBody246_35

def sourceBody246_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody246_36 sourceBody246_5

def sourceBody246_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody246_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.or [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.var 26])

def sourceBody246_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody246_41 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 20 (Flapjack.WordRegImm.reg 30) sourceBody246_40 sourceBody246_38

def sourceBody246_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody246_41 sourceBody246_5

def sourceBody246_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 20)

def sourceBody246_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 10#64)

def sourceBody246_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody246_46 : WordLangProgHOL (BitVec 64) :=
.call (some (([28]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody246_10, 246, 2)) (some 245) ([12]) (some (12, sourceBody246_45, 246, 3))

def sourceBody246_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody246_46 sourceBody246_5

def sourceBody246_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody246_47 sourceBody246_10

def sourceBody246_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody246_44 sourceBody246_48

def sourceBody246_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody246_10 sourceBody246_49

def sourceBody246_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody246_10 sourceBody246_50

def sourceBody246_52 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.imm 0#64) sourceBody246_51 sourceBody246_10

def sourceBody246_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody246_52 sourceBody246_5

def sourceBody246_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody246_53 sourceBody246_10

def sourceBody246_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody246_43 sourceBody246_54

def sourceBody246_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody246_42 sourceBody246_55

def sourceBody246_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody246_39 sourceBody246_56

def sourceBody246_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody246_38 sourceBody246_57

def sourceBody246_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody246_37 sourceBody246_58

def sourceBody246_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody246_33 sourceBody246_59

def sourceBody246_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody246_32 sourceBody246_60

def sourceBody246_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody246_31 sourceBody246_61

def sourceBody246_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody246_27 sourceBody246_62

def sourceBody246_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody246_7 sourceBody246_63

def sourceBody246_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 24)

def sourceBody246_66 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.less) 12 (Flapjack.WordRegImm.reg 22) sourceBody246_28 sourceBody246_29

def sourceBody246_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody246_66 sourceBody246_5

def sourceBody246_68 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 12)

def sourceBody246_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 24)
              (Flapjack.WordLangExpHOL.const 3#64)],
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody246_70 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 11#64)

def sourceBody246_71 : WordLangProgHOL (BitVec 64) :=
.call (some (([28]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody246_10, 246, 4)) (some 245) ([12]) (some (12, sourceBody246_45, 246, 5))

def sourceBody246_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody246_71 sourceBody246_5

def sourceBody246_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody246_72 sourceBody246_10

def sourceBody246_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody246_70 sourceBody246_73

def sourceBody246_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody246_10 sourceBody246_74

def sourceBody246_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody246_10 sourceBody246_75

def sourceBody246_77 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 16 (Flapjack.WordRegImm.imm 0#64) sourceBody246_76 sourceBody246_10

def sourceBody246_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody246_77 sourceBody246_5

def sourceBody246_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody246_78 sourceBody246_10

def sourceBody246_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody246_68 sourceBody246_79

def sourceBody246_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody246_31 sourceBody246_80

def sourceBody246_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody246_69 sourceBody246_81

def sourceBody246_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody246_7 sourceBody246_82

def sourceBody246_84 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 16 (Flapjack.WordRegImm.imm 0#64) sourceBody246_83 sourceBody246_10

def sourceBody246_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody246_84 sourceBody246_5

def sourceBody246_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody246_85 sourceBody246_10

def sourceBody246_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody246_68 sourceBody246_86

def sourceBody246_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody246_67 sourceBody246_87

def sourceBody246_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody246_65 sourceBody246_88

def sourceBody246_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody246_29 sourceBody246_89

def sourceBody246_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody246_64 sourceBody246_90

def sourceBody246_92 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 24, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody246_93 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 28)

def sourceBody246_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody246_93 sourceBody246_10

def sourceBody246_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody246_94 sourceBody246_10

def sourceBody246_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody246_92 sourceBody246_95

def sourceBody246_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody246_10 sourceBody246_96

def sourceBody246_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody246_91 sourceBody246_97

def sourceBody246_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody246_26 sourceBody246_98

def sourceBody246_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody246_10 sourceBody246_99

def sourceBody246_101 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody246_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody246_100 sourceBody246_101

def sourceBody246_103 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody246_104 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 22 (Flapjack.WordRegImm.imm 0#64) sourceBody246_102 sourceBody246_103

def sourceBody246_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody246_104 sourceBody246_5

def sourceBody246_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody246_105 sourceBody246_10

def sourceBody246_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody246_25 sourceBody246_106

def sourceBody246_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody246_24 sourceBody246_107

def sourceBody246_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody246_21 sourceBody246_108

def sourceBody246_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody246_20 sourceBody246_109

def sourceBody246_111 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
  PUnit.unit Flapjack.Spt.ln) sourceBody246_110 (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln)

def sourceBody246_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody246_111 sourceBody246_5

def sourceBody246_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody246_5 sourceBody246_112

def sourceBody246_114 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.load (Flapjack.WordLangExpHOL.var 2))

def sourceBody246_115 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 6)

def sourceBody246_116 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 28 (Flapjack.WordRegImm.reg 12) sourceBody246_22 sourceBody246_1

def sourceBody246_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody246_116 sourceBody246_5

def sourceBody246_118 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 12#64)

def sourceBody246_119 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 28

def sourceBody246_120 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody246_10, 246, 6)) (some 245) ([28]) (some (28, sourceBody246_119, 246, 7))

def sourceBody246_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody246_120 sourceBody246_5

def sourceBody246_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody246_121 sourceBody246_10

def sourceBody246_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody246_118 sourceBody246_122

def sourceBody246_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody246_10 sourceBody246_123

def sourceBody246_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody246_10 sourceBody246_124

def sourceBody246_126 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 22 (Flapjack.WordRegImm.imm 0#64) sourceBody246_125 sourceBody246_10

def sourceBody246_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody246_126 sourceBody246_5

def sourceBody246_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody246_127 sourceBody246_10

def sourceBody246_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody246_25 sourceBody246_128

def sourceBody246_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody246_117 sourceBody246_129

def sourceBody246_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody246_115 sourceBody246_130

def sourceBody246_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody246_114 sourceBody246_131

def sourceBody246_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody246_113 sourceBody246_132

def sourceBody246_134 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [18]

def sourceBody246_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody246_134 sourceBody246_10

def sourceBody246_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody246_3 sourceBody246_135

def sourceBody246_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody246_133 sourceBody246_136

def sourceBody246_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody246_8 sourceBody246_137

def sourceBody246_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody246_10 sourceBody246_138

def sourceBody246_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody246_19 sourceBody246_139

def source246 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (246, 5, sourceBody246_140)
end InitECandidate.Proofs.WordStages
