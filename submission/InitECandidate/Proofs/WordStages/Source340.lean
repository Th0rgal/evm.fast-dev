import InitECandidate.Proofs.WordStages.Source324
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody340_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody340_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 2)

def sourceBody340_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 4)

def sourceBody340_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 48

def sourceBody340_4 : WordLangProgHOL (BitVec 64) :=
.call (some (([56, 14]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody340_0, 340, 2)) (some 169) ([48, 32]) (some (48, sourceBody340_3, 340, 3))

def sourceBody340_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody340_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_4 sourceBody340_5

def sourceBody340_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_6 sourceBody340_0

def sourceBody340_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_2 sourceBody340_7

def sourceBody340_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_1 sourceBody340_8

def sourceBody340_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 14)

def sourceBody340_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 66 (Flapjack.WordLangExpHOL.const 120#64)

def sourceBody340_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.longMul 10 10 32 66))

def sourceBody340_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 10)

def sourceBody340_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 32

def sourceBody340_15 : WordLangProgHOL (BitVec 64) :=
.call (some (([48]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody340_0, 340, 4)) (some 68) ([44]) (some (32, sourceBody340_14, 340, 5))

def sourceBody340_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_15 sourceBody340_5

def sourceBody340_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_16 sourceBody340_0

def sourceBody340_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_13 sourceBody340_17

def sourceBody340_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_12 sourceBody340_18

def sourceBody340_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_11 sourceBody340_19

def sourceBody340_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_10 sourceBody340_20

def sourceBody340_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody340_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 32)

def sourceBody340_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 14)

def sourceBody340_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody340_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody340_27 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 10 (Flapjack.WordRegImm.reg 44) sourceBody340_25 sourceBody340_26

def sourceBody340_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_27 sourceBody340_5

def sourceBody340_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 10)

def sourceBody340_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 62
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 56,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 32)
          (Flapjack.WordLangExpHOL.const 4#64)]))

def sourceBody340_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 56,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 32)
          (Flapjack.WordLangExpHOL.const 4#64),
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody340_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 62

def sourceBody340_33 : WordLangProgHOL (BitVec 64) :=
.call (some (([66, 10, 44, 28]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody340_0, 340, 6)) (some 161) ([62, 20]) (some (62, sourceBody340_32, 340, 7))

def sourceBody340_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_33 sourceBody340_5

def sourceBody340_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_34 sourceBody340_0

def sourceBody340_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_31 sourceBody340_35

def sourceBody340_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_30 sourceBody340_36

def sourceBody340_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 66)

def sourceBody340_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody340_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody340_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody340_42 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 20 (Flapjack.WordRegImm.reg 52) sourceBody340_40 sourceBody340_41

def sourceBody340_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_42 sourceBody340_5

def sourceBody340_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 20)

def sourceBody340_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 62 (Flapjack.WordLangExpHOL.const 20#64)

def sourceBody340_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 62)

def sourceBody340_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_46 sourceBody340_0

def sourceBody340_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_47 sourceBody340_0

def sourceBody340_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_45 sourceBody340_48

def sourceBody340_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_0 sourceBody340_49

def sourceBody340_51 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 62 (Flapjack.WordLangExpHOL.const 6#64)

def sourceBody340_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_51 sourceBody340_32

def sourceBody340_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_50 sourceBody340_52

def sourceBody340_54 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 36 (Flapjack.WordRegImm.imm 0#64) sourceBody340_53 sourceBody340_0

def sourceBody340_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_54 sourceBody340_5

def sourceBody340_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_55 sourceBody340_0

def sourceBody340_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_44 sourceBody340_56

def sourceBody340_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_43 sourceBody340_57

def sourceBody340_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_39 sourceBody340_58

def sourceBody340_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_38 sourceBody340_59

def sourceBody340_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.var 10)

def sourceBody340_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 44)

def sourceBody340_63 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 52

def sourceBody340_64 : WordLangProgHOL (BitVec 64) :=
.call (some (([62, 20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody340_0, 340, 8)) (some 169) ([52, 36]) (some (52, sourceBody340_63, 340, 9))

def sourceBody340_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_64 sourceBody340_5

def sourceBody340_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_65 sourceBody340_0

def sourceBody340_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_62 sourceBody340_66

def sourceBody340_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_61 sourceBody340_67

def sourceBody340_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 70 (Flapjack.WordLangExpHOL.const 6#64)

def sourceBody340_70 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody340_71 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody340_72 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 36 (Flapjack.WordRegImm.reg 70) sourceBody340_70 sourceBody340_71

def sourceBody340_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_72 sourceBody340_5

def sourceBody340_74 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 36)

def sourceBody340_75 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.const 20#64)

def sourceBody340_76 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 52)

def sourceBody340_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_76 sourceBody340_0

def sourceBody340_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_77 sourceBody340_0

def sourceBody340_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_75 sourceBody340_78

def sourceBody340_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_0 sourceBody340_79

def sourceBody340_81 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.const 6#64)

def sourceBody340_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_81 sourceBody340_63

def sourceBody340_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_80 sourceBody340_82

def sourceBody340_84 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.WordRegImm.imm 0#64) sourceBody340_83 sourceBody340_0

def sourceBody340_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_84 sourceBody340_5

def sourceBody340_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_85 sourceBody340_0

def sourceBody340_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_74 sourceBody340_86

def sourceBody340_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_73 sourceBody340_87

def sourceBody340_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_69 sourceBody340_88

def sourceBody340_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_44 sourceBody340_89

def sourceBody340_91 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.var 32)

def sourceBody340_92 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.const 120#64)

def sourceBody340_93 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.longMul 70 70 52 36))

def sourceBody340_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_93 sourceBody340_0

def sourceBody340_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_92 sourceBody340_94

def sourceBody340_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_91 sourceBody340_95

def sourceBody340_97 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 48, Flapjack.WordLangExpHOL.var 70])

def sourceBody340_98 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 62)

def sourceBody340_99 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody340_100 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 68 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody340_101 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 50

def sourceBody340_102 : WordLangProgHOL (BitVec 64) :=
.call (some (([42, 26, 60, 18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln)
        Flapjack.Spt.ln)
      PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody340_0, 340, 10)) (some 332) ([50, 34, 68]) (some (50, sourceBody340_101, 340, 11))

def sourceBody340_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_102 sourceBody340_5

def sourceBody340_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_103 sourceBody340_0

def sourceBody340_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_100 sourceBody340_104

def sourceBody340_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_99 sourceBody340_105

def sourceBody340_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_98 sourceBody340_106

def sourceBody340_108 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 0#64])

def sourceBody340_109 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 42)

def sourceBody340_110 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 68 (Flapjack.WordLangExpHOL.var 26)

def sourceBody340_111 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 60)

def sourceBody340_112 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 18)

def sourceBody340_113 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 34)

def sourceBody340_114 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 50) 30

def sourceBody340_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_114 sourceBody340_0

def sourceBody340_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_113 sourceBody340_115

def sourceBody340_117 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 68)

def sourceBody340_118 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 50, Flapjack.WordLangExpHOL.const 8#64])
  30

def sourceBody340_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_118 sourceBody340_0

def sourceBody340_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_117 sourceBody340_119

def sourceBody340_121 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 12)

def sourceBody340_122 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 50, Flapjack.WordLangExpHOL.const 16#64])
  30

def sourceBody340_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_122 sourceBody340_0

def sourceBody340_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_121 sourceBody340_123

def sourceBody340_125 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 46)

def sourceBody340_126 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 50, Flapjack.WordLangExpHOL.const 24#64])
  30

def sourceBody340_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_126 sourceBody340_0

def sourceBody340_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_125 sourceBody340_127

def sourceBody340_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_128 sourceBody340_0

def sourceBody340_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_124 sourceBody340_129

def sourceBody340_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_120 sourceBody340_130

def sourceBody340_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_116 sourceBody340_131

def sourceBody340_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_112 sourceBody340_132

def sourceBody340_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_0 sourceBody340_133

def sourceBody340_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_111 sourceBody340_134

def sourceBody340_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_0 sourceBody340_135

def sourceBody340_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_110 sourceBody340_136

def sourceBody340_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_0 sourceBody340_137

def sourceBody340_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_109 sourceBody340_138

def sourceBody340_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_0 sourceBody340_139

def sourceBody340_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_108 sourceBody340_140

def sourceBody340_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_0 sourceBody340_141

def sourceBody340_143 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 62)

def sourceBody340_144 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 68 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody340_145 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 20#64)

def sourceBody340_146 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 34

def sourceBody340_147 : WordLangProgHOL (BitVec 64) :=
.call (some (([50]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln)
        Flapjack.Spt.ln)
      PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody340_0, 340, 12)) (some 335) ([34, 68, 12]) (some (34, sourceBody340_146, 340, 13))

def sourceBody340_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_147 sourceBody340_5

def sourceBody340_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_148 sourceBody340_0

def sourceBody340_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_145 sourceBody340_149

def sourceBody340_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_144 sourceBody340_150

def sourceBody340_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_143 sourceBody340_151

def sourceBody340_153 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 32#64])

def sourceBody340_154 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 68 (Flapjack.WordLangExpHOL.var 50)

def sourceBody340_155 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 68)

def sourceBody340_156 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 34) 12

def sourceBody340_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_156 sourceBody340_0

def sourceBody340_158 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_155 sourceBody340_157

def sourceBody340_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_158 sourceBody340_0

def sourceBody340_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_154 sourceBody340_159

def sourceBody340_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_0 sourceBody340_160

def sourceBody340_162 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_153 sourceBody340_161

def sourceBody340_163 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_0 sourceBody340_162

def sourceBody340_164 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 68 (Flapjack.WordLangExpHOL.var 62)

def sourceBody340_165 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 2#64)

def sourceBody340_166 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.const 8#64)

def sourceBody340_167 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 12#64)

def sourceBody340_168 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 68

def sourceBody340_169 : WordLangProgHOL (BitVec 64) :=
.call (some (([34]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln)
        Flapjack.Spt.ln)
      PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody340_0, 340, 14)) (some 333) ([68, 12, 46, 30]) (some (68, sourceBody340_168, 340, 15))

def sourceBody340_170 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_169 sourceBody340_5

def sourceBody340_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_170 sourceBody340_0

def sourceBody340_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_167 sourceBody340_171

def sourceBody340_173 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_166 sourceBody340_172

def sourceBody340_174 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_165 sourceBody340_173

def sourceBody340_175 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_164 sourceBody340_174

def sourceBody340_176 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 68
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 40#64])

def sourceBody340_177 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 34)

def sourceBody340_178 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 12)

def sourceBody340_179 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 68) 46

def sourceBody340_180 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_179 sourceBody340_0

def sourceBody340_181 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_178 sourceBody340_180

def sourceBody340_182 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_181 sourceBody340_0

def sourceBody340_183 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_177 sourceBody340_182

def sourceBody340_184 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_0 sourceBody340_183

def sourceBody340_185 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_176 sourceBody340_184

def sourceBody340_186 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_0 sourceBody340_185

def sourceBody340_187 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 3#64)

def sourceBody340_188 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody340_189 : WordLangProgHOL (BitVec 64) :=
.call (some (([34]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln)
        Flapjack.Spt.ln)
      PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody340_0, 340, 16)) (some 333) ([68, 12, 46, 30]) (some (68, sourceBody340_168, 340, 17))

def sourceBody340_190 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_189 sourceBody340_5

def sourceBody340_191 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_190 sourceBody340_0

def sourceBody340_192 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_167 sourceBody340_191

def sourceBody340_193 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_188 sourceBody340_192

def sourceBody340_194 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_187 sourceBody340_193

def sourceBody340_195 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_164 sourceBody340_194

def sourceBody340_196 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_186 sourceBody340_195

def sourceBody340_197 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 68
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 48#64])

def sourceBody340_198 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_197 sourceBody340_184

def sourceBody340_199 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_0 sourceBody340_198

def sourceBody340_200 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_196 sourceBody340_199

def sourceBody340_201 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 64 (Flapjack.WordLangExpHOL.var 62)

def sourceBody340_202 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 4#64)

def sourceBody340_203 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody340_204 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 64

def sourceBody340_205 : WordLangProgHOL (BitVec 64) :=
.call (some (([68, 12, 46, 30]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln)
        Flapjack.Spt.ln)
      PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody340_0, 340, 18)) (some 332) ([64, 22, 54]) (some (64, sourceBody340_204, 340, 19))

def sourceBody340_206 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_205 sourceBody340_5

def sourceBody340_207 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_206 sourceBody340_0

def sourceBody340_208 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_203 sourceBody340_207

def sourceBody340_209 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_202 sourceBody340_208

def sourceBody340_210 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_201 sourceBody340_209

def sourceBody340_211 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 64
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 56#64])

def sourceBody340_212 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 68)

def sourceBody340_213 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 12)

def sourceBody340_214 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 46)

def sourceBody340_215 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 72 (Flapjack.WordLangExpHOL.var 30)

def sourceBody340_216 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 22)

def sourceBody340_217 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 64) 6

def sourceBody340_218 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_217 sourceBody340_0

def sourceBody340_219 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_216 sourceBody340_218

def sourceBody340_220 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 54)

def sourceBody340_221 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 64, Flapjack.WordLangExpHOL.const 8#64]) 6

def sourceBody340_222 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_221 sourceBody340_0

def sourceBody340_223 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_220 sourceBody340_222

def sourceBody340_224 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 38)

def sourceBody340_225 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 64, Flapjack.WordLangExpHOL.const 16#64])
  6

def sourceBody340_226 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_225 sourceBody340_0

def sourceBody340_227 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_224 sourceBody340_226

def sourceBody340_228 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 72)

def sourceBody340_229 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 64, Flapjack.WordLangExpHOL.const 24#64])
  6

def sourceBody340_230 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_229 sourceBody340_0

def sourceBody340_231 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_228 sourceBody340_230

def sourceBody340_232 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_231 sourceBody340_0

def sourceBody340_233 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_227 sourceBody340_232

def sourceBody340_234 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_223 sourceBody340_233

def sourceBody340_235 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_219 sourceBody340_234

def sourceBody340_236 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_215 sourceBody340_235

def sourceBody340_237 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_0 sourceBody340_236

def sourceBody340_238 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_214 sourceBody340_237

def sourceBody340_239 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_0 sourceBody340_238

def sourceBody340_240 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_213 sourceBody340_239

def sourceBody340_241 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_0 sourceBody340_240

def sourceBody340_242 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_212 sourceBody340_241

def sourceBody340_243 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_0 sourceBody340_242

def sourceBody340_244 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_211 sourceBody340_243

def sourceBody340_245 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_0 sourceBody340_244

def sourceBody340_246 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 72 (Flapjack.WordLangExpHOL.var 62)

def sourceBody340_247 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 5#64)

def sourceBody340_248 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody340_249 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 72

def sourceBody340_250 : WordLangProgHOL (BitVec 64) :=
.call (some (([64, 22, 54, 38]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody340_0, 340, 20)) (some 332) ([72, 6, 40]) (some (72, sourceBody340_249, 340, 21))

def sourceBody340_251 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_250 sourceBody340_5

def sourceBody340_252 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_251 sourceBody340_0

def sourceBody340_253 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_248 sourceBody340_252

def sourceBody340_254 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_247 sourceBody340_253

def sourceBody340_255 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_246 sourceBody340_254

def sourceBody340_256 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 72
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 88#64])

def sourceBody340_257 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 64)

def sourceBody340_258 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 22)

def sourceBody340_259 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 54)

def sourceBody340_260 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.var 38)

def sourceBody340_261 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 6)

def sourceBody340_262 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 72) 16

def sourceBody340_263 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_262 sourceBody340_0

def sourceBody340_264 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_261 sourceBody340_263

def sourceBody340_265 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 40)

def sourceBody340_266 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 72, Flapjack.WordLangExpHOL.const 8#64])
  16

def sourceBody340_267 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_266 sourceBody340_0

def sourceBody340_268 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_265 sourceBody340_267

def sourceBody340_269 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 24)

def sourceBody340_270 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 72, Flapjack.WordLangExpHOL.const 16#64])
  16

def sourceBody340_271 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_270 sourceBody340_0

def sourceBody340_272 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_269 sourceBody340_271

def sourceBody340_273 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 58)

def sourceBody340_274 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 72, Flapjack.WordLangExpHOL.const 24#64])
  16

def sourceBody340_275 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_274 sourceBody340_0

def sourceBody340_276 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_273 sourceBody340_275

def sourceBody340_277 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_276 sourceBody340_0

def sourceBody340_278 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_272 sourceBody340_277

def sourceBody340_279 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_268 sourceBody340_278

def sourceBody340_280 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_264 sourceBody340_279

def sourceBody340_281 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_260 sourceBody340_280

def sourceBody340_282 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_0 sourceBody340_281

def sourceBody340_283 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_259 sourceBody340_282

def sourceBody340_284 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_0 sourceBody340_283

def sourceBody340_285 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_258 sourceBody340_284

def sourceBody340_286 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_0 sourceBody340_285

def sourceBody340_287 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_257 sourceBody340_286

def sourceBody340_288 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_0 sourceBody340_287

def sourceBody340_289 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_256 sourceBody340_288

def sourceBody340_290 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_0 sourceBody340_289

def sourceBody340_291 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 72
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 32, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody340_292 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 72)

def sourceBody340_293 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_292 sourceBody340_0

def sourceBody340_294 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_293 sourceBody340_0

def sourceBody340_295 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_291 sourceBody340_294

def sourceBody340_296 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_0 sourceBody340_295

def sourceBody340_297 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_290 sourceBody340_296

def sourceBody340_298 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_255 sourceBody340_297

def sourceBody340_299 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_0 sourceBody340_298

def sourceBody340_300 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_0 sourceBody340_299

def sourceBody340_301 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_0 sourceBody340_300

def sourceBody340_302 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_0 sourceBody340_301

def sourceBody340_303 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_0 sourceBody340_302

def sourceBody340_304 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_0 sourceBody340_303

def sourceBody340_305 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_0 sourceBody340_304

def sourceBody340_306 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_0 sourceBody340_305

def sourceBody340_307 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_245 sourceBody340_306

def sourceBody340_308 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_210 sourceBody340_307

def sourceBody340_309 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_0 sourceBody340_308

def sourceBody340_310 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_0 sourceBody340_309

def sourceBody340_311 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_0 sourceBody340_310

def sourceBody340_312 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_0 sourceBody340_311

def sourceBody340_313 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_0 sourceBody340_312

def sourceBody340_314 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_0 sourceBody340_313

def sourceBody340_315 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_0 sourceBody340_314

def sourceBody340_316 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_0 sourceBody340_315

def sourceBody340_317 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_200 sourceBody340_316

def sourceBody340_318 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_175 sourceBody340_317

def sourceBody340_319 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_0 sourceBody340_318

def sourceBody340_320 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_0 sourceBody340_319

def sourceBody340_321 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_163 sourceBody340_320

def sourceBody340_322 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_152 sourceBody340_321

def sourceBody340_323 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_0 sourceBody340_322

def sourceBody340_324 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_0 sourceBody340_323

def sourceBody340_325 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_142 sourceBody340_324

def sourceBody340_326 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_107 sourceBody340_325

def sourceBody340_327 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_0 sourceBody340_326

def sourceBody340_328 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_0 sourceBody340_327

def sourceBody340_329 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_0 sourceBody340_328

def sourceBody340_330 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_0 sourceBody340_329

def sourceBody340_331 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_0 sourceBody340_330

def sourceBody340_332 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_0 sourceBody340_331

def sourceBody340_333 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_0 sourceBody340_332

def sourceBody340_334 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_0 sourceBody340_333

def sourceBody340_335 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_97 sourceBody340_334

def sourceBody340_336 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_96 sourceBody340_335

def sourceBody340_337 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_90 sourceBody340_336

def sourceBody340_338 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_68 sourceBody340_337

def sourceBody340_339 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_0 sourceBody340_338

def sourceBody340_340 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_0 sourceBody340_339

def sourceBody340_341 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_0 sourceBody340_340

def sourceBody340_342 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_0 sourceBody340_341

def sourceBody340_343 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_60 sourceBody340_342

def sourceBody340_344 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_37 sourceBody340_343

def sourceBody340_345 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_0 sourceBody340_344

def sourceBody340_346 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_0 sourceBody340_345

def sourceBody340_347 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_0 sourceBody340_346

def sourceBody340_348 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_0 sourceBody340_347

def sourceBody340_349 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_0 sourceBody340_348

def sourceBody340_350 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_0 sourceBody340_349

def sourceBody340_351 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_0 sourceBody340_350

def sourceBody340_352 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_0 sourceBody340_351

def sourceBody340_353 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody340_354 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_352 sourceBody340_353

def sourceBody340_355 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody340_356 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 28 (Flapjack.WordRegImm.imm 0#64) sourceBody340_354 sourceBody340_355

def sourceBody340_357 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_356 sourceBody340_5

def sourceBody340_358 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_357 sourceBody340_0

def sourceBody340_359 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_29 sourceBody340_358

def sourceBody340_360 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_28 sourceBody340_359

def sourceBody340_361 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_24 sourceBody340_360

def sourceBody340_362 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_23 sourceBody340_361

def sourceBody340_363 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))))
  PUnit.unit Flapjack.Spt.ln) sourceBody340_362 (Flapjack.Spt.bs
  (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody340_364 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_363 sourceBody340_5

def sourceBody340_365 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_5 sourceBody340_364

def sourceBody340_366 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 66 (Flapjack.WordLangExpHOL.var 48)

def sourceBody340_367 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 14)

def sourceBody340_368 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [66, 10]

def sourceBody340_369 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_368 sourceBody340_0

def sourceBody340_370 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_367 sourceBody340_369

def sourceBody340_371 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_366 sourceBody340_370

def sourceBody340_372 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_365 sourceBody340_371

def sourceBody340_373 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_22 sourceBody340_372

def sourceBody340_374 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_0 sourceBody340_373

def sourceBody340_375 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_21 sourceBody340_374

def sourceBody340_376 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_0 sourceBody340_375

def sourceBody340_377 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_0 sourceBody340_376

def sourceBody340_378 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_9 sourceBody340_377

def sourceBody340_379 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_0 sourceBody340_378

def sourceBody340_380 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_0 sourceBody340_379

def sourceBody340_381 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_0 sourceBody340_380

def sourceBody340_382 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody340_0 sourceBody340_381

def source340 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (340, 3, sourceBody340_382)
end InitECandidate.Proofs.WordStages
