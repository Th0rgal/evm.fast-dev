import InitECandidate.Proofs.WordStages.Source617
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody633_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody633_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody633_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody633_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 20)

def sourceBody633_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.var 8])

def sourceBody633_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody633_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody633_7 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 14 (Flapjack.WordRegImm.reg 26) sourceBody633_5 sourceBody633_6

def sourceBody633_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_7 sourceBody633_2

def sourceBody633_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 14)

def sourceBody633_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 10,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 20)
        (Flapjack.WordLangExpHOL.const 3#64)])

def sourceBody633_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 14)

def sourceBody633_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 32) 26

def sourceBody633_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_12 sourceBody633_0

def sourceBody633_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_11 sourceBody633_13

def sourceBody633_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_14 sourceBody633_0

def sourceBody633_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_6 sourceBody633_15

def sourceBody633_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_0 sourceBody633_16

def sourceBody633_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_10 sourceBody633_17

def sourceBody633_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_0 sourceBody633_18

def sourceBody633_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 20, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody633_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 32)

def sourceBody633_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_21 sourceBody633_0

def sourceBody633_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_22 sourceBody633_0

def sourceBody633_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_20 sourceBody633_23

def sourceBody633_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_0 sourceBody633_24

def sourceBody633_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_19 sourceBody633_25

def sourceBody633_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody633_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_26 sourceBody633_27

def sourceBody633_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody633_30 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 18 (Flapjack.WordRegImm.imm 0#64) sourceBody633_28 sourceBody633_29

def sourceBody633_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_30 sourceBody633_2

def sourceBody633_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_31 sourceBody633_0

def sourceBody633_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_9 sourceBody633_32

def sourceBody633_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_8 sourceBody633_33

def sourceBody633_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_4 sourceBody633_34

def sourceBody633_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_3 sourceBody633_35

def sourceBody633_37 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit Flapjack.Spt.ln) sourceBody633_36 (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody633_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_37 sourceBody633_2

def sourceBody633_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_2 sourceBody633_38

def sourceBody633_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_1 sourceBody633_0

def sourceBody633_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_40 sourceBody633_0

def sourceBody633_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_39 sourceBody633_41

def sourceBody633_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 4)

def sourceBody633_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 20)
          (Flapjack.WordLangExpHOL.const 3#64)]))

def sourceBody633_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody633_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 10,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 20)
        (Flapjack.WordLangExpHOL.const 3#64)])

def sourceBody633_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 26)

def sourceBody633_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 8)

def sourceBody633_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody633_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody633_51 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 16 (Flapjack.WordRegImm.reg 28) sourceBody633_49 sourceBody633_50

def sourceBody633_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_51 sourceBody633_2

def sourceBody633_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 16)

def sourceBody633_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 32)

def sourceBody633_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 6,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 26)
          (Flapjack.WordLangExpHOL.const 3#64)]))

def sourceBody633_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.longMul 28 28 30 16))

def sourceBody633_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_56 sourceBody633_0

def sourceBody633_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_55 sourceBody633_57

def sourceBody633_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_54 sourceBody633_58

def sourceBody633_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 28,
      Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 18,
            Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 26)
              (Flapjack.WordLangExpHOL.const 3#64)]),
      Flapjack.WordLangExpHOL.var 14])

def sourceBody633_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 18,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 26)
        (Flapjack.WordLangExpHOL.const 3#64)])

def sourceBody633_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and
    [Flapjack.WordLangExpHOL.var 22, Flapjack.WordLangExpHOL.const 4294967295#64])

def sourceBody633_63 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 12)

def sourceBody633_64 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 34) 24

def sourceBody633_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_64 sourceBody633_0

def sourceBody633_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_63 sourceBody633_65

def sourceBody633_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_66 sourceBody633_0

def sourceBody633_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_62 sourceBody633_67

def sourceBody633_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_0 sourceBody633_68

def sourceBody633_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_61 sourceBody633_69

def sourceBody633_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_0 sourceBody633_70

def sourceBody633_72 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr (Flapjack.WordLangExpHOL.var 22)
    (Flapjack.WordLangExpHOL.const 32#64))

def sourceBody633_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_72 sourceBody633_0

def sourceBody633_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_73 sourceBody633_0

def sourceBody633_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_71 sourceBody633_74

def sourceBody633_76 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 26, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody633_77 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 34)

def sourceBody633_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_77 sourceBody633_0

def sourceBody633_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_78 sourceBody633_0

def sourceBody633_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_76 sourceBody633_79

def sourceBody633_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_0 sourceBody633_80

def sourceBody633_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_75 sourceBody633_81

def sourceBody633_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_60 sourceBody633_82

def sourceBody633_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_59 sourceBody633_83

def sourceBody633_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_84 sourceBody633_27

def sourceBody633_86 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 22 (Flapjack.WordRegImm.imm 0#64) sourceBody633_85 sourceBody633_29

def sourceBody633_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_86 sourceBody633_2

def sourceBody633_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_87 sourceBody633_0

def sourceBody633_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_53 sourceBody633_88

def sourceBody633_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_52 sourceBody633_89

def sourceBody633_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_48 sourceBody633_90

def sourceBody633_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_47 sourceBody633_91

def sourceBody633_93 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
  PUnit.unit Flapjack.Spt.ln) sourceBody633_92 (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody633_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_93 sourceBody633_2

def sourceBody633_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_2 sourceBody633_94

def sourceBody633_96 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 18,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 8)
        (Flapjack.WordLangExpHOL.const 3#64)])

def sourceBody633_97 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 14)

def sourceBody633_98 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 16)

def sourceBody633_99 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 30) 28

def sourceBody633_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_99 sourceBody633_0

def sourceBody633_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_98 sourceBody633_100

def sourceBody633_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_101 sourceBody633_0

def sourceBody633_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_97 sourceBody633_102

def sourceBody633_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_0 sourceBody633_103

def sourceBody633_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_96 sourceBody633_104

def sourceBody633_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_0 sourceBody633_105

def sourceBody633_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_95 sourceBody633_106

def sourceBody633_108 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 20, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody633_109 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 30)

def sourceBody633_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_109 sourceBody633_0

def sourceBody633_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_110 sourceBody633_0

def sourceBody633_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_108 sourceBody633_111

def sourceBody633_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_0 sourceBody633_112

def sourceBody633_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_107 sourceBody633_113

def sourceBody633_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_46 sourceBody633_114

def sourceBody633_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_0 sourceBody633_115

def sourceBody633_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_45 sourceBody633_116

def sourceBody633_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_0 sourceBody633_117

def sourceBody633_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_6 sourceBody633_118

def sourceBody633_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_0 sourceBody633_119

def sourceBody633_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_44 sourceBody633_120

def sourceBody633_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_0 sourceBody633_121

def sourceBody633_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_122 sourceBody633_27

def sourceBody633_124 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 18 (Flapjack.WordRegImm.imm 0#64) sourceBody633_123 sourceBody633_29

def sourceBody633_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_124 sourceBody633_2

def sourceBody633_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_125 sourceBody633_0

def sourceBody633_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_9 sourceBody633_126

def sourceBody633_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_8 sourceBody633_127

def sourceBody633_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_43 sourceBody633_128

def sourceBody633_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_3 sourceBody633_129

def sourceBody633_131 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit Flapjack.Spt.ln) sourceBody633_130 (Flapjack.Spt.ls PUnit.unit)

def sourceBody633_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_131 sourceBody633_2

def sourceBody633_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_2 sourceBody633_132

def sourceBody633_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_42 sourceBody633_133

def sourceBody633_135 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody633_136 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [32]

def sourceBody633_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_136 sourceBody633_0

def sourceBody633_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_135 sourceBody633_137

def sourceBody633_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_134 sourceBody633_138

def sourceBody633_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_1 sourceBody633_139

def sourceBody633_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody633_0 sourceBody633_140

def source633 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (633, 6, sourceBody633_141)
end InitECandidate.Proofs.WordStages
