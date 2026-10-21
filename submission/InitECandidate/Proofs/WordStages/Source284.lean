import InitECandidate.Proofs.WordStages.Source268
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody284_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody284_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody284_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody284_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 4)

def sourceBody284_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 4#64])

def sourceBody284_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody284_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody284_7 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notLower) 16 (Flapjack.WordRegImm.reg 28) sourceBody284_5 sourceBody284_6

def sourceBody284_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody284_7 sourceBody284_2

def sourceBody284_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 16)

def sourceBody284_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.var 10])

def sourceBody284_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 22 (Flapjack.WordLangAddr.addr 22 0#64))

def sourceBody284_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody284_11 sourceBody284_0

def sourceBody284_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody284_10 sourceBody284_12

def sourceBody284_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 22)

def sourceBody284_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 6,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 10)
        (Flapjack.WordLangExpHOL.const 1#64)])

def sourceBody284_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr (Flapjack.WordLangExpHOL.var 16)
    (Flapjack.WordLangExpHOL.const 4#64))

def sourceBody284_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.store8 8 (Flapjack.WordLangAddr.addr 28 0#64))

def sourceBody284_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody284_17 sourceBody284_0

def sourceBody284_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody284_16 sourceBody284_18

def sourceBody284_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody284_15 sourceBody284_19

def sourceBody284_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 6,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 10)
        (Flapjack.WordLangExpHOL.const 1#64),
      Flapjack.WordLangExpHOL.const 1#64])

def sourceBody284_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and [Flapjack.WordLangExpHOL.var 16, Flapjack.WordLangExpHOL.const 15#64])

def sourceBody284_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody284_22 sourceBody284_18

def sourceBody284_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody284_21 sourceBody284_23

def sourceBody284_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody284_20 sourceBody284_24

def sourceBody284_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody284_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 28 (Flapjack.WordLangAddr.addr 28 0#64))

def sourceBody284_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody284_27 sourceBody284_0

def sourceBody284_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody284_26 sourceBody284_28

def sourceBody284_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 28)

def sourceBody284_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 6,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 10)
        (Flapjack.WordLangExpHOL.const 1#64),
      Flapjack.WordLangExpHOL.const 2#64])

def sourceBody284_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr (Flapjack.WordLangExpHOL.var 8)
    (Flapjack.WordLangExpHOL.const 4#64))

def sourceBody284_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.store8 14 (Flapjack.WordLangAddr.addr 20 0#64))

def sourceBody284_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody284_33 sourceBody284_0

def sourceBody284_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody284_32 sourceBody284_34

def sourceBody284_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody284_31 sourceBody284_35

def sourceBody284_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 6,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 10)
        (Flapjack.WordLangExpHOL.const 1#64),
      Flapjack.WordLangExpHOL.const 3#64])

def sourceBody284_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 15#64])

def sourceBody284_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody284_38 sourceBody284_34

def sourceBody284_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody284_37 sourceBody284_39

def sourceBody284_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody284_36 sourceBody284_40

def sourceBody284_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 2#64])

def sourceBody284_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 20 (Flapjack.WordLangAddr.addr 20 0#64))

def sourceBody284_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody284_43 sourceBody284_0

def sourceBody284_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody284_42 sourceBody284_44

def sourceBody284_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 20)

def sourceBody284_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 6,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 10)
        (Flapjack.WordLangExpHOL.const 1#64),
      Flapjack.WordLangExpHOL.const 4#64])

def sourceBody284_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr (Flapjack.WordLangExpHOL.var 14)
    (Flapjack.WordLangExpHOL.const 4#64))

def sourceBody284_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.store8 12 (Flapjack.WordLangAddr.addr 26 0#64))

def sourceBody284_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody284_49 sourceBody284_0

def sourceBody284_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody284_48 sourceBody284_50

def sourceBody284_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody284_47 sourceBody284_51

def sourceBody284_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 6,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 10)
        (Flapjack.WordLangExpHOL.const 1#64),
      Flapjack.WordLangExpHOL.const 5#64])

def sourceBody284_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 15#64])

def sourceBody284_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody284_54 sourceBody284_50

def sourceBody284_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody284_53 sourceBody284_55

def sourceBody284_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody284_52 sourceBody284_56

def sourceBody284_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 3#64])

def sourceBody284_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 26 (Flapjack.WordLangAddr.addr 26 0#64))

def sourceBody284_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody284_59 sourceBody284_0

def sourceBody284_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody284_58 sourceBody284_60

def sourceBody284_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 26)

def sourceBody284_63 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 6,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 10)
        (Flapjack.WordLangExpHOL.const 1#64),
      Flapjack.WordLangExpHOL.const 6#64])

def sourceBody284_64 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr (Flapjack.WordLangExpHOL.var 12)
    (Flapjack.WordLangExpHOL.const 4#64))

def sourceBody284_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.store8 18 (Flapjack.WordLangAddr.addr 24 0#64))

def sourceBody284_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody284_65 sourceBody284_0

def sourceBody284_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody284_64 sourceBody284_66

def sourceBody284_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody284_63 sourceBody284_67

def sourceBody284_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 6,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 10)
        (Flapjack.WordLangExpHOL.const 1#64),
      Flapjack.WordLangExpHOL.const 7#64])

def sourceBody284_70 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 15#64])

def sourceBody284_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody284_70 sourceBody284_66

def sourceBody284_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody284_69 sourceBody284_71

def sourceBody284_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody284_68 sourceBody284_72

def sourceBody284_74 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 4#64])

def sourceBody284_75 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 24)

def sourceBody284_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody284_75 sourceBody284_0

def sourceBody284_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody284_76 sourceBody284_0

def sourceBody284_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody284_74 sourceBody284_77

def sourceBody284_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody284_0 sourceBody284_78

def sourceBody284_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody284_73 sourceBody284_79

def sourceBody284_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody284_62 sourceBody284_80

def sourceBody284_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody284_61 sourceBody284_81

def sourceBody284_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody284_57 sourceBody284_82

def sourceBody284_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody284_46 sourceBody284_83

def sourceBody284_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody284_45 sourceBody284_84

def sourceBody284_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody284_41 sourceBody284_85

def sourceBody284_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody284_30 sourceBody284_86

def sourceBody284_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody284_29 sourceBody284_87

def sourceBody284_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody284_25 sourceBody284_88

def sourceBody284_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody284_14 sourceBody284_89

def sourceBody284_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody284_13 sourceBody284_90

def sourceBody284_92 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody284_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody284_91 sourceBody284_92

def sourceBody284_94 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody284_95 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.WordRegImm.imm 0#64) sourceBody284_93 sourceBody284_94

def sourceBody284_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody284_95 sourceBody284_2

def sourceBody284_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody284_96 sourceBody284_0

def sourceBody284_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody284_9 sourceBody284_97

def sourceBody284_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody284_8 sourceBody284_98

def sourceBody284_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody284_4 sourceBody284_99

def sourceBody284_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody284_3 sourceBody284_100

def sourceBody284_102 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.ls PUnit.unit))
  PUnit.unit Flapjack.Spt.ln) sourceBody284_101 (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.ls PUnit.unit))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody284_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody284_102 sourceBody284_2

def sourceBody284_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody284_2 sourceBody284_103

def sourceBody284_105 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 10)

def sourceBody284_106 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 4)

def sourceBody284_107 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 16 (Flapjack.WordRegImm.reg 28) sourceBody284_5 sourceBody284_6

def sourceBody284_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody284_107 sourceBody284_2

def sourceBody284_109 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody284_110 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 28)

def sourceBody284_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody284_110 sourceBody284_0

def sourceBody284_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody284_111 sourceBody284_0

def sourceBody284_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody284_109 sourceBody284_112

def sourceBody284_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody284_0 sourceBody284_113

def sourceBody284_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody284_25 sourceBody284_114

def sourceBody284_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody284_14 sourceBody284_115

def sourceBody284_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody284_13 sourceBody284_116

def sourceBody284_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody284_117 sourceBody284_92

def sourceBody284_119 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.WordRegImm.imm 0#64) sourceBody284_118 sourceBody284_94

def sourceBody284_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody284_119 sourceBody284_2

def sourceBody284_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody284_120 sourceBody284_0

def sourceBody284_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody284_9 sourceBody284_121

def sourceBody284_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody284_108 sourceBody284_122

def sourceBody284_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody284_106 sourceBody284_123

def sourceBody284_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody284_105 sourceBody284_124

def sourceBody284_126 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    (Flapjack.Spt.ls PUnit.unit))
  PUnit.unit Flapjack.Spt.ln) sourceBody284_125 (Flapjack.Spt.ls PUnit.unit)

def sourceBody284_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody284_126 sourceBody284_2

def sourceBody284_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody284_2 sourceBody284_127

def sourceBody284_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody284_104 sourceBody284_128

def sourceBody284_130 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody284_131 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [22]

def sourceBody284_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody284_131 sourceBody284_0

def sourceBody284_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody284_130 sourceBody284_132

def sourceBody284_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody284_129 sourceBody284_133

def sourceBody284_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody284_1 sourceBody284_134

def sourceBody284_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody284_0 sourceBody284_135

def source284 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (284, 4, sourceBody284_136)
end InitECandidate.Proofs.WordStages
