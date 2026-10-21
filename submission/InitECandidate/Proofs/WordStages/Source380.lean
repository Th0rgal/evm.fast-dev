import InitECandidate.Proofs.WordStages.Source364
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody380_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody380_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 192#64]))

def sourceBody380_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 200#64]))

def sourceBody380_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 36)

def sourceBody380_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 10)

def sourceBody380_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody380_6 : WordLangProgHOL (BitVec 64) :=
.call (some (([30]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody380_0, 380, 2)) (some 379) ([20, 42]) (some (20, sourceBody380_5, 380, 3))

def sourceBody380_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody380_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_6 sourceBody380_7

def sourceBody380_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_8 sourceBody380_0

def sourceBody380_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_4 sourceBody380_9

def sourceBody380_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_3 sourceBody380_10

def sourceBody380_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 30)
    (Flapjack.WordLangExpHOL.const 2#64))

def sourceBody380_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 152#64]))

def sourceBody380_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 160#64]))

def sourceBody380_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 160#64],
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody380_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 160#64],
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody380_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 160#64],
        Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody380_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 28

def sourceBody380_19 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody380_0, 380, 4)) (some 102) ([28, 18, 40, 14]) (some (28, sourceBody380_18, 380, 5))

def sourceBody380_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_19 sourceBody380_7

def sourceBody380_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_20 sourceBody380_0

def sourceBody380_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_17 sourceBody380_21

def sourceBody380_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_16 sourceBody380_22

def sourceBody380_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_15 sourceBody380_23

def sourceBody380_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_14 sourceBody380_24

def sourceBody380_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody380_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody380_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 42)

def sourceBody380_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody380_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody380_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody380_32 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 14 (Flapjack.WordRegImm.reg 34) sourceBody380_30 sourceBody380_31

def sourceBody380_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_32 sourceBody380_7

def sourceBody380_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 14)

def sourceBody380_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 12000#64)

def sourceBody380_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_35 sourceBody380_0

def sourceBody380_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_36 sourceBody380_0

def sourceBody380_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
    (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr
      (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
        [Flapjack.WordLangExpHOL.var 10, Flapjack.WordLangExpHOL.const 31#64])
      (Flapjack.WordLangExpHOL.const 5#64))
    (Flapjack.WordLangExpHOL.const 1#64))

def sourceBody380_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_38 sourceBody380_0

def sourceBody380_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_39 sourceBody380_0

def sourceBody380_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_37 sourceBody380_40

def sourceBody380_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 4)

def sourceBody380_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 20#64)

def sourceBody380_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody380_45 : WordLangProgHOL (BitVec 64) :=
.call (some (([40]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody380_0, 380, 6)) (some 79) ([14, 34, 24]) (some (14, sourceBody380_44, 380, 7))

def sourceBody380_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_45 sourceBody380_7

def sourceBody380_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_46 sourceBody380_0

def sourceBody380_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_43 sourceBody380_47

def sourceBody380_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_42 sourceBody380_48

def sourceBody380_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_28 sourceBody380_49

def sourceBody380_51 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 40)

def sourceBody380_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody380_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody380_54 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 34 (Flapjack.WordRegImm.reg 24) sourceBody380_53 sourceBody380_29

def sourceBody380_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_54 sourceBody380_7

def sourceBody380_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 34)

def sourceBody380_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 3000#64)

def sourceBody380_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_57 sourceBody380_0

def sourceBody380_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_58 sourceBody380_0

def sourceBody380_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 8)

def sourceBody380_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 28, Flapjack.WordLangExpHOL.const 6000#64])

def sourceBody380_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 14)

def sourceBody380_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_62 sourceBody380_0

def sourceBody380_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_63 sourceBody380_0

def sourceBody380_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_61 sourceBody380_64

def sourceBody380_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_0 sourceBody380_65

def sourceBody380_67 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 46 (Flapjack.WordRegImm.imm 0#64) sourceBody380_66 sourceBody380_0

def sourceBody380_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_67 sourceBody380_7

def sourceBody380_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_68 sourceBody380_0

def sourceBody380_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_56 sourceBody380_69

def sourceBody380_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_55 sourceBody380_70

def sourceBody380_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_52 sourceBody380_71

def sourceBody380_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_60 sourceBody380_72

def sourceBody380_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_59 sourceBody380_73

def sourceBody380_75 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 46 (Flapjack.WordRegImm.imm 0#64) sourceBody380_74 sourceBody380_0

def sourceBody380_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_75 sourceBody380_7

def sourceBody380_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_76 sourceBody380_0

def sourceBody380_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_56 sourceBody380_77

def sourceBody380_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_55 sourceBody380_78

def sourceBody380_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_52 sourceBody380_79

def sourceBody380_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_51 sourceBody380_80

def sourceBody380_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_50 sourceBody380_81

def sourceBody380_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_0 sourceBody380_82

def sourceBody380_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_0 sourceBody380_83

def sourceBody380_85 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 24 (Flapjack.WordRegImm.imm 0#64) sourceBody380_41 sourceBody380_84

def sourceBody380_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_85 sourceBody380_7

def sourceBody380_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_86 sourceBody380_0

def sourceBody380_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_34 sourceBody380_87

def sourceBody380_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_33 sourceBody380_88

def sourceBody380_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_29 sourceBody380_89

def sourceBody380_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_28 sourceBody380_90

def sourceBody380_92 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody380_93 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 0#64]))

def sourceBody380_94 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody380_95 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody380_96 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 24 (Flapjack.WordRegImm.reg 46) sourceBody380_95 sourceBody380_52

def sourceBody380_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_96 sourceBody380_7

def sourceBody380_98 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 24)

def sourceBody380_99 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 208#64]))

def sourceBody380_100 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 216#64]))

def sourceBody380_101 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 46)

def sourceBody380_102 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 24)

def sourceBody380_103 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody380_104 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody380_105 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 26 (Flapjack.WordRegImm.reg 16) sourceBody380_103 sourceBody380_104

def sourceBody380_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_105 sourceBody380_7

def sourceBody380_107 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 26)

def sourceBody380_108 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 46)

def sourceBody380_109 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 24#64)

def sourceBody380_110 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.longMul 16 16 6 26))

def sourceBody380_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_110 sourceBody380_0

def sourceBody380_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_109 sourceBody380_111

def sourceBody380_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_108 sourceBody380_112

def sourceBody380_114 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 34, Flapjack.WordLangExpHOL.var 16, Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody380_115 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 38)

def sourceBody380_116 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
    [Flapjack.WordLangExpHOL.const 2100#64, Flapjack.WordLangExpHOL.const 100#64])

def sourceBody380_117 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.longMul 22 22 12 32))

def sourceBody380_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_117 sourceBody380_0

def sourceBody380_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_116 sourceBody380_118

def sourceBody380_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_115 sourceBody380_119

def sourceBody380_121 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 40,
      Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
        [Flapjack.WordLangExpHOL.const 3000#64, Flapjack.WordLangExpHOL.const 100#64],
      Flapjack.WordLangExpHOL.var 22])

def sourceBody380_122 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 44)

def sourceBody380_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_122 sourceBody380_0

def sourceBody380_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_123 sourceBody380_0

def sourceBody380_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_121 sourceBody380_124

def sourceBody380_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_120 sourceBody380_125

def sourceBody380_127 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 80#64,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 38)
        (Flapjack.WordLangExpHOL.const 7#64)])

def sourceBody380_128 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 12)

def sourceBody380_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_128 sourceBody380_0

def sourceBody380_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_129 sourceBody380_0

def sourceBody380_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_127 sourceBody380_130

def sourceBody380_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_0 sourceBody380_131

def sourceBody380_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_126 sourceBody380_132

def sourceBody380_134 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 46, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody380_135 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 12)

def sourceBody380_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_135 sourceBody380_0

def sourceBody380_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_136 sourceBody380_0

def sourceBody380_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_134 sourceBody380_137

def sourceBody380_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_0 sourceBody380_138

def sourceBody380_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_133 sourceBody380_139

def sourceBody380_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_114 sourceBody380_140

def sourceBody380_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_113 sourceBody380_141

def sourceBody380_143 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody380_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_142 sourceBody380_143

def sourceBody380_145 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody380_146 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 38 (Flapjack.WordRegImm.imm 0#64) sourceBody380_144 sourceBody380_145

def sourceBody380_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_146 sourceBody380_7

def sourceBody380_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_147 sourceBody380_0

def sourceBody380_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_107 sourceBody380_148

def sourceBody380_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_106 sourceBody380_149

def sourceBody380_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_102 sourceBody380_150

def sourceBody380_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_101 sourceBody380_151

def sourceBody380_153 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        Flapjack.Spt.ln)
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        Flapjack.Spt.ln)))
  PUnit.unit Flapjack.Spt.ln) sourceBody380_152 (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit
    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody380_154 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_153 sourceBody380_7

def sourceBody380_155 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_7 sourceBody380_154

def sourceBody380_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_94 sourceBody380_155

def sourceBody380_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_0 sourceBody380_156

def sourceBody380_158 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_100 sourceBody380_157

def sourceBody380_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_0 sourceBody380_158

def sourceBody380_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_99 sourceBody380_159

def sourceBody380_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_0 sourceBody380_160

def sourceBody380_162 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.WordRegImm.imm 0#64) sourceBody380_161 sourceBody380_0

def sourceBody380_163 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_162 sourceBody380_7

def sourceBody380_164 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_163 sourceBody380_0

def sourceBody380_165 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_98 sourceBody380_164

def sourceBody380_166 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_97 sourceBody380_165

def sourceBody380_167 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_94 sourceBody380_166

def sourceBody380_168 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_93 sourceBody380_167

def sourceBody380_169 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 40,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 14)
        (Flapjack.WordLangExpHOL.const 4#64)])

def sourceBody380_170 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 34)

def sourceBody380_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_170 sourceBody380_0

def sourceBody380_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_171 sourceBody380_0

def sourceBody380_173 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_169 sourceBody380_172

def sourceBody380_174 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_0 sourceBody380_173

def sourceBody380_175 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_168 sourceBody380_174

def sourceBody380_176 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 0#64]))

def sourceBody380_177 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 4#64)

def sourceBody380_178 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody380_179 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 46 (Flapjack.WordRegImm.reg 6) sourceBody380_178 sourceBody380_94

def sourceBody380_180 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_179 sourceBody380_7

def sourceBody380_181 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 280#64]))

def sourceBody380_182 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.const 7816#64)

def sourceBody380_183 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.longMul 6 6 24 46))

def sourceBody380_184 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 6)

def sourceBody380_185 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_184 sourceBody380_0

def sourceBody380_186 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_183 sourceBody380_185

def sourceBody380_187 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_182 sourceBody380_186

def sourceBody380_188 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_181 sourceBody380_187

def sourceBody380_189 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_188 sourceBody380_0

def sourceBody380_190 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 26 (Flapjack.WordRegImm.imm 0#64) sourceBody380_189 sourceBody380_0

def sourceBody380_191 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_190 sourceBody380_7

def sourceBody380_192 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_191 sourceBody380_0

def sourceBody380_193 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_101 sourceBody380_192

def sourceBody380_194 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_180 sourceBody380_193

def sourceBody380_195 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_177 sourceBody380_194

def sourceBody380_196 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_176 sourceBody380_195

def sourceBody380_197 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 10)
    (Flapjack.WordLangExpHOL.const 2#64))

def sourceBody380_198 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 24, Flapjack.WordLangExpHOL.var 14])

def sourceBody380_199 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.const 12000#64, Flapjack.WordLangExpHOL.var 28])

def sourceBody380_200 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.var 20,
      Flapjack.WordLangExpHOL.var 40, Flapjack.WordLangExpHOL.var 34])

def sourceBody380_201 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 46)
        (Flapjack.WordLangExpHOL.const 4#64),
      Flapjack.WordLangExpHOL.var 6])

def sourceBody380_202 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody380_203 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 16)

def sourceBody380_204 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [38, 12, 32]

def sourceBody380_205 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_204 sourceBody380_0

def sourceBody380_206 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_203 sourceBody380_205

def sourceBody380_207 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_202 sourceBody380_206

def sourceBody380_208 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_107 sourceBody380_207

def sourceBody380_209 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_201 sourceBody380_208

def sourceBody380_210 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_0 sourceBody380_209

def sourceBody380_211 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_200 sourceBody380_210

def sourceBody380_212 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_0 sourceBody380_211

def sourceBody380_213 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_199 sourceBody380_212

def sourceBody380_214 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_0 sourceBody380_213

def sourceBody380_215 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_198 sourceBody380_214

def sourceBody380_216 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_0 sourceBody380_215

def sourceBody380_217 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_197 sourceBody380_216

def sourceBody380_218 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_0 sourceBody380_217

def sourceBody380_219 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_196 sourceBody380_218

def sourceBody380_220 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_29 sourceBody380_219

def sourceBody380_221 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_0 sourceBody380_220

def sourceBody380_222 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_175 sourceBody380_221

def sourceBody380_223 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_31 sourceBody380_222

def sourceBody380_224 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_0 sourceBody380_223

def sourceBody380_225 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_92 sourceBody380_224

def sourceBody380_226 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_0 sourceBody380_225

def sourceBody380_227 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_91 sourceBody380_226

def sourceBody380_228 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_27 sourceBody380_227

def sourceBody380_229 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_0 sourceBody380_228

def sourceBody380_230 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_26 sourceBody380_229

def sourceBody380_231 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_0 sourceBody380_230

def sourceBody380_232 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_25 sourceBody380_231

def sourceBody380_233 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_0 sourceBody380_232

def sourceBody380_234 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_0 sourceBody380_233

def sourceBody380_235 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_13 sourceBody380_234

def sourceBody380_236 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_0 sourceBody380_235

def sourceBody380_237 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_12 sourceBody380_236

def sourceBody380_238 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_0 sourceBody380_237

def sourceBody380_239 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_11 sourceBody380_238

def sourceBody380_240 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_0 sourceBody380_239

def sourceBody380_241 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_0 sourceBody380_240

def sourceBody380_242 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_2 sourceBody380_241

def sourceBody380_243 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_0 sourceBody380_242

def sourceBody380_244 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_1 sourceBody380_243

def sourceBody380_245 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody380_0 sourceBody380_244

def source380 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (380, 3, sourceBody380_245)
end InitECandidate.Proofs.WordStages
