import InitECandidate.Proofs.WordStages.Source322
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody338_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody338_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 2)

def sourceBody338_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 4)

def sourceBody338_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 36

def sourceBody338_4 : WordLangProgHOL (BitVec 64) :=
.call (some (([42, 12]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody338_0, 338, 2)) (some 169) ([36, 24]) (some (36, sourceBody338_3, 338, 3))

def sourceBody338_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody338_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_4 sourceBody338_5

def sourceBody338_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_6 sourceBody338_0

def sourceBody338_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_2 sourceBody338_7

def sourceBody338_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_1 sourceBody338_8

def sourceBody338_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 12)

def sourceBody338_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.const 24#64)

def sourceBody338_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.longMul 8 8 24 48))

def sourceBody338_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 8)

def sourceBody338_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 24

def sourceBody338_15 : WordLangProgHOL (BitVec 64) :=
.call (some (([36]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
      PUnit.unit (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody338_0, 338, 4)) (some 68) ([32]) (some (24, sourceBody338_14, 338, 5))

def sourceBody338_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_15 sourceBody338_5

def sourceBody338_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_16 sourceBody338_0

def sourceBody338_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_13 sourceBody338_17

def sourceBody338_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_12 sourceBody338_18

def sourceBody338_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_11 sourceBody338_19

def sourceBody338_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_10 sourceBody338_20

def sourceBody338_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody338_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 24)

def sourceBody338_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 12)

def sourceBody338_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody338_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody338_27 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 8 (Flapjack.WordRegImm.reg 32) sourceBody338_25 sourceBody338_26

def sourceBody338_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_27 sourceBody338_5

def sourceBody338_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 8)

def sourceBody338_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 42,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 24)
          (Flapjack.WordLangExpHOL.const 4#64)]))

def sourceBody338_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 42,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 24)
          (Flapjack.WordLangExpHOL.const 4#64),
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody338_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 46

def sourceBody338_33 : WordLangProgHOL (BitVec 64) :=
.call (some (([48, 8, 32, 20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody338_0, 338, 6)) (some 161) ([46, 16]) (some (46, sourceBody338_32, 338, 7))

def sourceBody338_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_33 sourceBody338_5

def sourceBody338_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_34 sourceBody338_0

def sourceBody338_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_31 sourceBody338_35

def sourceBody338_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_30 sourceBody338_36

def sourceBody338_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 48)

def sourceBody338_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody338_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody338_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody338_42 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 16 (Flapjack.WordRegImm.reg 40) sourceBody338_40 sourceBody338_41

def sourceBody338_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_42 sourceBody338_5

def sourceBody338_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 16)

def sourceBody338_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.const 19#64)

def sourceBody338_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 46)

def sourceBody338_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_46 sourceBody338_0

def sourceBody338_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_47 sourceBody338_0

def sourceBody338_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_45 sourceBody338_48

def sourceBody338_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_0 sourceBody338_49

def sourceBody338_51 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.const 6#64)

def sourceBody338_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_51 sourceBody338_32

def sourceBody338_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_50 sourceBody338_52

def sourceBody338_54 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 28 (Flapjack.WordRegImm.imm 0#64) sourceBody338_53 sourceBody338_0

def sourceBody338_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_54 sourceBody338_5

def sourceBody338_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_55 sourceBody338_0

def sourceBody338_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_44 sourceBody338_56

def sourceBody338_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_43 sourceBody338_57

def sourceBody338_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_39 sourceBody338_58

def sourceBody338_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_38 sourceBody338_59

def sourceBody338_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 8)

def sourceBody338_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 32)

def sourceBody338_63 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 40

def sourceBody338_64 : WordLangProgHOL (BitVec 64) :=
.call (some (([46, 16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody338_0, 338, 8)) (some 169) ([40, 28]) (some (40, sourceBody338_63, 338, 9))

def sourceBody338_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_64 sourceBody338_5

def sourceBody338_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_65 sourceBody338_0

def sourceBody338_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_62 sourceBody338_66

def sourceBody338_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_61 sourceBody338_67

def sourceBody338_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.const 2#64)

def sourceBody338_70 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody338_71 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody338_72 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 28 (Flapjack.WordRegImm.reg 52) sourceBody338_70 sourceBody338_71

def sourceBody338_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_72 sourceBody338_5

def sourceBody338_74 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 28)

def sourceBody338_75 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.const 19#64)

def sourceBody338_76 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 40)

def sourceBody338_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_76 sourceBody338_0

def sourceBody338_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_77 sourceBody338_0

def sourceBody338_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_75 sourceBody338_78

def sourceBody338_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_0 sourceBody338_79

def sourceBody338_81 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.const 6#64)

def sourceBody338_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_81 sourceBody338_63

def sourceBody338_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_80 sourceBody338_82

def sourceBody338_84 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.WordRegImm.imm 0#64) sourceBody338_83 sourceBody338_0

def sourceBody338_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_84 sourceBody338_5

def sourceBody338_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_85 sourceBody338_0

def sourceBody338_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_74 sourceBody338_86

def sourceBody338_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_73 sourceBody338_87

def sourceBody338_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_69 sourceBody338_88

def sourceBody338_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_44 sourceBody338_89

def sourceBody338_91 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 46)

def sourceBody338_92 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody338_93 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 20#64)

def sourceBody338_94 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 28

def sourceBody338_95 : WordLangProgHOL (BitVec 64) :=
.call (some (([40]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody338_0, 338, 10)) (some 335) ([28, 52, 6]) (some (28, sourceBody338_94, 338, 11))

def sourceBody338_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_95 sourceBody338_5

def sourceBody338_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_96 sourceBody338_0

def sourceBody338_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_93 sourceBody338_97

def sourceBody338_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_92 sourceBody338_98

def sourceBody338_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_91 sourceBody338_99

def sourceBody338_101 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 46)

def sourceBody338_102 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody338_103 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody338_104 : WordLangProgHOL (BitVec 64) :=
.call (some (([28, 52]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody338_0, 338, 12)) (some 337) ([6, 30]) (some (6, sourceBody338_103, 338, 13))

def sourceBody338_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_104 sourceBody338_5

def sourceBody338_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_105 sourceBody338_0

def sourceBody338_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_102 sourceBody338_106

def sourceBody338_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_101 sourceBody338_107

def sourceBody338_109 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 28)

def sourceBody338_110 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 52)

def sourceBody338_111 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody338_112 : WordLangProgHOL (BitVec 64) :=
.call (some (([6, 30]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody338_0, 338, 14)) (some 169) ([18, 44]) (some (18, sourceBody338_111, 338, 15))

def sourceBody338_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_112 sourceBody338_5

def sourceBody338_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_113 sourceBody338_0

def sourceBody338_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_110 sourceBody338_114

def sourceBody338_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_109 sourceBody338_115

def sourceBody338_117 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44
  (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 30)
    (Flapjack.WordLangExpHOL.const 5#64))

def sourceBody338_118 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 44

def sourceBody338_119 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody338_0, 338, 16)) (some 68) ([44]) (some (44, sourceBody338_118, 338, 17))

def sourceBody338_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_119 sourceBody338_5

def sourceBody338_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_120 sourceBody338_0

def sourceBody338_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_117 sourceBody338_121

def sourceBody338_123 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody338_124 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 44)

def sourceBody338_125 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 30)

def sourceBody338_126 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody338_127 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody338_128 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 38 (Flapjack.WordRegImm.reg 26) sourceBody338_126 sourceBody338_127

def sourceBody338_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_128 sourceBody338_5

def sourceBody338_130 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 38)

def sourceBody338_131 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 6)

def sourceBody338_132 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 44)

def sourceBody338_133 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody338_134 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 38

def sourceBody338_135 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody338_0, 338, 18)) (some 335) ([38, 26, 50]) (some (38, sourceBody338_134, 338, 19))

def sourceBody338_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_135 sourceBody338_5

def sourceBody338_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_136 sourceBody338_0

def sourceBody338_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_133 sourceBody338_137

def sourceBody338_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_132 sourceBody338_138

def sourceBody338_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_131 sourceBody338_139

def sourceBody338_141 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 18,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 44)
        (Flapjack.WordLangExpHOL.const 5#64)])

def sourceBody338_142 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 14)

def sourceBody338_143 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody338_144 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 26

def sourceBody338_145 : WordLangProgHOL (BitVec 64) :=
.call (some (([38]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody338_0, 338, 20)) (some 77) ([26, 50, 10]) (some (26, sourceBody338_144, 338, 21))

def sourceBody338_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_145 sourceBody338_5

def sourceBody338_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_146 sourceBody338_0

def sourceBody338_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_143 sourceBody338_147

def sourceBody338_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_142 sourceBody338_148

def sourceBody338_150 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_141 sourceBody338_149

def sourceBody338_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_0 sourceBody338_150

def sourceBody338_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_0 sourceBody338_151

def sourceBody338_153 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 44, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody338_154 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 38)

def sourceBody338_155 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_154 sourceBody338_0

def sourceBody338_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_155 sourceBody338_0

def sourceBody338_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_153 sourceBody338_156

def sourceBody338_158 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_0 sourceBody338_157

def sourceBody338_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_152 sourceBody338_158

def sourceBody338_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_140 sourceBody338_159

def sourceBody338_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_0 sourceBody338_160

def sourceBody338_162 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_0 sourceBody338_161

def sourceBody338_163 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody338_164 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_162 sourceBody338_163

def sourceBody338_165 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody338_166 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 50 (Flapjack.WordRegImm.imm 0#64) sourceBody338_164 sourceBody338_165

def sourceBody338_167 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_166 sourceBody338_5

def sourceBody338_168 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_167 sourceBody338_0

def sourceBody338_169 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_130 sourceBody338_168

def sourceBody338_170 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_129 sourceBody338_169

def sourceBody338_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_125 sourceBody338_170

def sourceBody338_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_124 sourceBody338_171

def sourceBody338_173 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
      PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
  PUnit.unit Flapjack.Spt.ln) sourceBody338_172 (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody338_174 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_173 sourceBody338_5

def sourceBody338_175 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_5 sourceBody338_174

def sourceBody338_176 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 24)

def sourceBody338_177 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.const 24#64)

def sourceBody338_178 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.longMul 26 26 14 38))

def sourceBody338_179 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_178 sourceBody338_0

def sourceBody338_180 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_177 sourceBody338_179

def sourceBody338_181 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_176 sourceBody338_180

def sourceBody338_182 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 36, Flapjack.WordLangExpHOL.var 26])

def sourceBody338_183 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 50, Flapjack.WordLangExpHOL.const 0#64])

def sourceBody338_184 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 40)

def sourceBody338_185 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 34)

def sourceBody338_186 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 10) 22

def sourceBody338_187 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_186 sourceBody338_0

def sourceBody338_188 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_185 sourceBody338_187

def sourceBody338_189 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_188 sourceBody338_0

def sourceBody338_190 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_184 sourceBody338_189

def sourceBody338_191 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_0 sourceBody338_190

def sourceBody338_192 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_183 sourceBody338_191

def sourceBody338_193 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_0 sourceBody338_192

def sourceBody338_194 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 50, Flapjack.WordLangExpHOL.const 8#64])

def sourceBody338_195 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 18)

def sourceBody338_196 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_195 sourceBody338_189

def sourceBody338_197 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_0 sourceBody338_196

def sourceBody338_198 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_194 sourceBody338_197

def sourceBody338_199 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_0 sourceBody338_198

def sourceBody338_200 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_193 sourceBody338_199

def sourceBody338_201 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 50, Flapjack.WordLangExpHOL.const 16#64])

def sourceBody338_202 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 30)

def sourceBody338_203 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_202 sourceBody338_189

def sourceBody338_204 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_0 sourceBody338_203

def sourceBody338_205 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_201 sourceBody338_204

def sourceBody338_206 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_0 sourceBody338_205

def sourceBody338_207 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_200 sourceBody338_206

def sourceBody338_208 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 24, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody338_209 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 10)

def sourceBody338_210 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_209 sourceBody338_0

def sourceBody338_211 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_210 sourceBody338_0

def sourceBody338_212 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_208 sourceBody338_211

def sourceBody338_213 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_0 sourceBody338_212

def sourceBody338_214 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_207 sourceBody338_213

def sourceBody338_215 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_182 sourceBody338_214

def sourceBody338_216 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_181 sourceBody338_215

def sourceBody338_217 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_175 sourceBody338_216

def sourceBody338_218 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_123 sourceBody338_217

def sourceBody338_219 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_0 sourceBody338_218

def sourceBody338_220 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_122 sourceBody338_219

def sourceBody338_221 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_0 sourceBody338_220

def sourceBody338_222 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_0 sourceBody338_221

def sourceBody338_223 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_116 sourceBody338_222

def sourceBody338_224 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_0 sourceBody338_223

def sourceBody338_225 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_0 sourceBody338_224

def sourceBody338_226 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_0 sourceBody338_225

def sourceBody338_227 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_0 sourceBody338_226

def sourceBody338_228 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_108 sourceBody338_227

def sourceBody338_229 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_0 sourceBody338_228

def sourceBody338_230 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_0 sourceBody338_229

def sourceBody338_231 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_0 sourceBody338_230

def sourceBody338_232 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_0 sourceBody338_231

def sourceBody338_233 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_100 sourceBody338_232

def sourceBody338_234 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_0 sourceBody338_233

def sourceBody338_235 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_0 sourceBody338_234

def sourceBody338_236 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_90 sourceBody338_235

def sourceBody338_237 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_68 sourceBody338_236

def sourceBody338_238 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_0 sourceBody338_237

def sourceBody338_239 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_0 sourceBody338_238

def sourceBody338_240 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_0 sourceBody338_239

def sourceBody338_241 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_0 sourceBody338_240

def sourceBody338_242 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_60 sourceBody338_241

def sourceBody338_243 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_37 sourceBody338_242

def sourceBody338_244 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_0 sourceBody338_243

def sourceBody338_245 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_0 sourceBody338_244

def sourceBody338_246 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_0 sourceBody338_245

def sourceBody338_247 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_0 sourceBody338_246

def sourceBody338_248 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_0 sourceBody338_247

def sourceBody338_249 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_0 sourceBody338_248

def sourceBody338_250 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_0 sourceBody338_249

def sourceBody338_251 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_0 sourceBody338_250

def sourceBody338_252 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_251 sourceBody338_163

def sourceBody338_253 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 20 (Flapjack.WordRegImm.imm 0#64) sourceBody338_252 sourceBody338_165

def sourceBody338_254 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_253 sourceBody338_5

def sourceBody338_255 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_254 sourceBody338_0

def sourceBody338_256 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_29 sourceBody338_255

def sourceBody338_257 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_28 sourceBody338_256

def sourceBody338_258 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_24 sourceBody338_257

def sourceBody338_259 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_23 sourceBody338_258

def sourceBody338_260 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
    PUnit.unit
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
  PUnit.unit Flapjack.Spt.ln) sourceBody338_259 (Flapjack.Spt.bs
  (Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      Flapjack.Spt.ln))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody338_261 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_260 sourceBody338_5

def sourceBody338_262 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_5 sourceBody338_261

def sourceBody338_263 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 36)

def sourceBody338_264 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 12)

def sourceBody338_265 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [48, 8]

def sourceBody338_266 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_265 sourceBody338_0

def sourceBody338_267 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_264 sourceBody338_266

def sourceBody338_268 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_263 sourceBody338_267

def sourceBody338_269 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_262 sourceBody338_268

def sourceBody338_270 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_22 sourceBody338_269

def sourceBody338_271 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_0 sourceBody338_270

def sourceBody338_272 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_21 sourceBody338_271

def sourceBody338_273 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_0 sourceBody338_272

def sourceBody338_274 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_0 sourceBody338_273

def sourceBody338_275 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_9 sourceBody338_274

def sourceBody338_276 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_0 sourceBody338_275

def sourceBody338_277 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_0 sourceBody338_276

def sourceBody338_278 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_0 sourceBody338_277

def sourceBody338_279 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody338_0 sourceBody338_278

def source338 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (338, 3, sourceBody338_279)
end InitECandidate.Proofs.WordStages
