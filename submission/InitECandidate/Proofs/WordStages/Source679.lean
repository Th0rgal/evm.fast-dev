import InitECandidate.Proofs.WordStages.Source663
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody679_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody679_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44
  (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 2)
    (Flapjack.WordLangExpHOL.const 5#64))

def sourceBody679_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.var 2)

def sourceBody679_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 6,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 44)
        (Flapjack.WordLangExpHOL.const 1#64)])

def sourceBody679_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 58

def sourceBody679_5 : WordLangProgHOL (BitVec 64) :=
.call (some (([30]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
        PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody679_0, 679, 2)) (some 672) ([58, 14]) (some (58, sourceBody679_4, 679, 3))

def sourceBody679_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody679_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_5 sourceBody679_6

def sourceBody679_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_7 sourceBody679_0

def sourceBody679_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_3 sourceBody679_8

def sourceBody679_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_2 sourceBody679_9

def sourceBody679_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 30)

def sourceBody679_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody679_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody679_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody679_15 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 14 (Flapjack.WordRegImm.reg 40) sourceBody679_13 sourceBody679_14

def sourceBody679_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_15 sourceBody679_6

def sourceBody679_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 14)

def sourceBody679_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 44)

def sourceBody679_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.const 3#64)

def sourceBody679_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.longMul 26 26 14 40))

def sourceBody679_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 4)

def sourceBody679_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 8)

def sourceBody679_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 26)

def sourceBody679_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody679_25 : WordLangProgHOL (BitVec 64) :=
.call (some (([58]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody679_0, 679, 4)) (some 77) ([54, 20, 48]) (some (14, sourceBody679_24, 679, 5))

def sourceBody679_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_25 sourceBody679_6

def sourceBody679_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_26 sourceBody679_0

def sourceBody679_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_23 sourceBody679_27

def sourceBody679_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_22 sourceBody679_28

def sourceBody679_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_21 sourceBody679_29

def sourceBody679_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_20 sourceBody679_30

def sourceBody679_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_19 sourceBody679_31

def sourceBody679_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_18 sourceBody679_32

def sourceBody679_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_33

def sourceBody679_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_34

def sourceBody679_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody679_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [58]

def sourceBody679_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_37 sourceBody679_0

def sourceBody679_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_36 sourceBody679_38

def sourceBody679_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_35 sourceBody679_39

def sourceBody679_41 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 26 (Flapjack.WordRegImm.imm 0#64) sourceBody679_40 sourceBody679_0

def sourceBody679_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_41 sourceBody679_6

def sourceBody679_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_42 sourceBody679_0

def sourceBody679_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_17 sourceBody679_43

def sourceBody679_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_16 sourceBody679_44

def sourceBody679_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_12 sourceBody679_45

def sourceBody679_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_11 sourceBody679_46

def sourceBody679_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 2)

def sourceBody679_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 8,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 44)
        (Flapjack.WordLangExpHOL.const 1#64)])

def sourceBody679_50 : WordLangProgHOL (BitVec 64) :=
.call (some (([58]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
        PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody679_0, 679, 6)) (some 672) ([14, 40]) (some (14, sourceBody679_24, 679, 7))

def sourceBody679_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_50 sourceBody679_6

def sourceBody679_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_51 sourceBody679_0

def sourceBody679_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_49 sourceBody679_52

def sourceBody679_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_48 sourceBody679_53

def sourceBody679_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 58)

def sourceBody679_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody679_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody679_58 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 40 (Flapjack.WordRegImm.reg 26) sourceBody679_12 sourceBody679_57

def sourceBody679_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_58 sourceBody679_6

def sourceBody679_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 40)

def sourceBody679_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 44)

def sourceBody679_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 3#64)

def sourceBody679_63 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.longMul 54 54 40 26))

def sourceBody679_64 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 4)

def sourceBody679_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48 (Flapjack.WordLangExpHOL.var 6)

def sourceBody679_66 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 54)

def sourceBody679_67 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 40

def sourceBody679_68 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody679_0, 679, 8)) (some 77) ([20, 48, 34]) (some (40, sourceBody679_67, 679, 9))

def sourceBody679_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_68 sourceBody679_6

def sourceBody679_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_69 sourceBody679_0

def sourceBody679_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_66 sourceBody679_70

def sourceBody679_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_65 sourceBody679_71

def sourceBody679_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_64 sourceBody679_72

def sourceBody679_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_63 sourceBody679_73

def sourceBody679_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_62 sourceBody679_74

def sourceBody679_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_61 sourceBody679_75

def sourceBody679_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_76

def sourceBody679_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_77

def sourceBody679_79 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [14]

def sourceBody679_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_79 sourceBody679_0

def sourceBody679_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_14 sourceBody679_80

def sourceBody679_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_78 sourceBody679_81

def sourceBody679_83 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 54 (Flapjack.WordRegImm.imm 0#64) sourceBody679_82 sourceBody679_0

def sourceBody679_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_83 sourceBody679_6

def sourceBody679_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_84 sourceBody679_0

def sourceBody679_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_60 sourceBody679_85

def sourceBody679_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_59 sourceBody679_86

def sourceBody679_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_56 sourceBody679_87

def sourceBody679_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_55 sourceBody679_88

def sourceBody679_90 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
        PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody679_0, 679, 10)) (some 69) ([]) (some (40, sourceBody679_67, 679, 11))

def sourceBody679_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_90 sourceBody679_6

def sourceBody679_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_91 sourceBody679_0

def sourceBody679_93 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 6)

def sourceBody679_94 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.var 44])

def sourceBody679_95 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 6,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 44)
        (Flapjack.WordLangExpHOL.const 1#64)])

def sourceBody679_96 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.var 44])

def sourceBody679_97 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 8,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 44)
        (Flapjack.WordLangExpHOL.const 1#64)])

def sourceBody679_98 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 44)

def sourceBody679_99 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody679_100 : WordLangProgHOL (BitVec 64) :=
.call (some (([62]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) (Flapjack.Spt.ls PUnit.unit))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody679_0, 679, 12)) (some 68) ([12]) (some (12, sourceBody679_99, 679, 13))

def sourceBody679_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_100 sourceBody679_6

def sourceBody679_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_101 sourceBody679_0

def sourceBody679_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_98 sourceBody679_102

def sourceBody679_104 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 44)

def sourceBody679_105 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 38

def sourceBody679_106 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) (Flapjack.Spt.ls PUnit.unit))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody679_0, 679, 14)) (some 68) ([38]) (some (38, sourceBody679_105, 679, 15))

def sourceBody679_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_106 sourceBody679_6

def sourceBody679_108 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_107 sourceBody679_0

def sourceBody679_109 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_104 sourceBody679_108

def sourceBody679_110 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 44)

def sourceBody679_111 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 24

def sourceBody679_112 : WordLangProgHOL (BitVec 64) :=
.call (some (([38]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.ls PUnit.unit))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody679_0, 679, 16)) (some 68) ([24]) (some (24, sourceBody679_111, 679, 17))

def sourceBody679_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_112 sourceBody679_6

def sourceBody679_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_113 sourceBody679_0

def sourceBody679_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_110 sourceBody679_114

def sourceBody679_116 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.var 44)

def sourceBody679_117 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 52

def sourceBody679_118 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.ls PUnit.unit))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody679_0, 679, 18)) (some 68) ([52]) (some (52, sourceBody679_117, 679, 19))

def sourceBody679_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_118 sourceBody679_6

def sourceBody679_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_119 sourceBody679_0

def sourceBody679_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_116 sourceBody679_120

def sourceBody679_122 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 2)

def sourceBody679_123 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 62)

def sourceBody679_124 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 48)

def sourceBody679_125 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 60 (Flapjack.WordLangExpHOL.var 54)

def sourceBody679_126 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody679_127 : WordLangProgHOL (BitVec 64) :=
.call (some (([52]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.ls PUnit.unit))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody679_0, 679, 20)) (some 666) ([18, 46, 32, 60]) (some (18, sourceBody679_126, 679, 21))

def sourceBody679_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_127 sourceBody679_6

def sourceBody679_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_128 sourceBody679_0

def sourceBody679_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_125 sourceBody679_129

def sourceBody679_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_124 sourceBody679_130

def sourceBody679_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_123 sourceBody679_131

def sourceBody679_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_122 sourceBody679_132

def sourceBody679_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_133

def sourceBody679_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_134

def sourceBody679_136 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 12)

def sourceBody679_137 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 26)

def sourceBody679_138 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 60 (Flapjack.WordLangExpHOL.var 34)

def sourceBody679_139 : WordLangProgHOL (BitVec 64) :=
.call (some (([52]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.ls PUnit.unit))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody679_0, 679, 22)) (some 666) ([18, 46, 32, 60]) (some (18, sourceBody679_126, 679, 23))

def sourceBody679_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_139 sourceBody679_6

def sourceBody679_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_140 sourceBody679_0

def sourceBody679_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_138 sourceBody679_141

def sourceBody679_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_137 sourceBody679_142

def sourceBody679_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_136 sourceBody679_143

def sourceBody679_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_122 sourceBody679_144

def sourceBody679_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_145

def sourceBody679_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_146

def sourceBody679_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_135 sourceBody679_147

def sourceBody679_149 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 38)

def sourceBody679_150 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 20)

def sourceBody679_151 : WordLangProgHOL (BitVec 64) :=
.call (some (([52]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody679_0, 679, 24)) (some 666) ([18, 46, 32, 60]) (some (18, sourceBody679_126, 679, 25))

def sourceBody679_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_151 sourceBody679_6

def sourceBody679_153 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_152 sourceBody679_0

def sourceBody679_154 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_125 sourceBody679_153

def sourceBody679_155 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_150 sourceBody679_154

def sourceBody679_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_149 sourceBody679_155

def sourceBody679_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_122 sourceBody679_156

def sourceBody679_158 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_157

def sourceBody679_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_158

def sourceBody679_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_148 sourceBody679_159

def sourceBody679_161 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 24)

def sourceBody679_162 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 40)

def sourceBody679_163 : WordLangProgHOL (BitVec 64) :=
.call (some (([52]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody679_0, 679, 26)) (some 666) ([18, 46, 32, 60]) (some (18, sourceBody679_126, 679, 27))

def sourceBody679_164 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_163 sourceBody679_6

def sourceBody679_165 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_164 sourceBody679_0

def sourceBody679_166 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_138 sourceBody679_165

def sourceBody679_167 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_162 sourceBody679_166

def sourceBody679_168 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_161 sourceBody679_167

def sourceBody679_169 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_122 sourceBody679_168

def sourceBody679_170 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_169

def sourceBody679_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_170

def sourceBody679_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_160 sourceBody679_171

def sourceBody679_173 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 24)

def sourceBody679_174 : WordLangProgHOL (BitVec 64) :=
.call (some (([52]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody679_0, 679, 28)) (some 673) ([18, 46, 32]) (some (18, sourceBody679_126, 679, 29))

def sourceBody679_175 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_174 sourceBody679_6

def sourceBody679_176 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_175 sourceBody679_0

def sourceBody679_177 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_173 sourceBody679_176

def sourceBody679_178 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_149 sourceBody679_177

def sourceBody679_179 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_122 sourceBody679_178

def sourceBody679_180 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 52)

def sourceBody679_181 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody679_182 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody679_183 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody679_184 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 46 (Flapjack.WordRegImm.reg 32) sourceBody679_182 sourceBody679_183

def sourceBody679_185 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_184 sourceBody679_6

def sourceBody679_186 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 60 (Flapjack.WordLangExpHOL.var 46)

def sourceBody679_187 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 2)

def sourceBody679_188 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 62)

def sourceBody679_189 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 60 (Flapjack.WordLangExpHOL.var 12)

def sourceBody679_190 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 46

def sourceBody679_191 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
      (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody679_0, 679, 30)) (some 673) ([46, 32, 60]) (some (46, sourceBody679_190, 679, 31))

def sourceBody679_192 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_191 sourceBody679_6

def sourceBody679_193 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_192 sourceBody679_0

def sourceBody679_194 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_189 sourceBody679_193

def sourceBody679_195 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_188 sourceBody679_194

def sourceBody679_196 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_187 sourceBody679_195

def sourceBody679_197 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 14)

def sourceBody679_198 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 32

def sourceBody679_199 : WordLangProgHOL (BitVec 64) :=
.call (some (([46]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody679_0, 679, 32)) (some 70) ([32]) (some (32, sourceBody679_198, 679, 33))

def sourceBody679_200 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_199 sourceBody679_6

def sourceBody679_201 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_200 sourceBody679_0

def sourceBody679_202 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_197 sourceBody679_201

def sourceBody679_203 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_202

def sourceBody679_204 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_203

def sourceBody679_205 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 18)

def sourceBody679_206 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 60 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody679_207 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody679_208 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 32 (Flapjack.WordRegImm.reg 60) sourceBody679_181 sourceBody679_207

def sourceBody679_209 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_208 sourceBody679_6

def sourceBody679_210 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 32)

def sourceBody679_211 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 2)

def sourceBody679_212 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 60 (Flapjack.WordLangExpHOL.var 4)

def sourceBody679_213 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 6)

def sourceBody679_214 : WordLangProgHOL (BitVec 64) :=
.call (some (([46]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody679_0, 679, 34)) (some 678) ([32, 60, 16]) (some (32, sourceBody679_198, 679, 35))

def sourceBody679_215 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_214 sourceBody679_6

def sourceBody679_216 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_215 sourceBody679_0

def sourceBody679_217 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_213 sourceBody679_216

def sourceBody679_218 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_212 sourceBody679_217

def sourceBody679_219 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_211 sourceBody679_218

def sourceBody679_220 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_219

def sourceBody679_221 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_220

def sourceBody679_222 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [46]

def sourceBody679_223 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_222 sourceBody679_0

def sourceBody679_224 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_183 sourceBody679_223

def sourceBody679_225 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_221 sourceBody679_224

def sourceBody679_226 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 16 (Flapjack.WordRegImm.imm 0#64) sourceBody679_225 sourceBody679_0

def sourceBody679_227 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_226 sourceBody679_6

def sourceBody679_228 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_227 sourceBody679_0

def sourceBody679_229 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_210 sourceBody679_228

def sourceBody679_230 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_209 sourceBody679_229

def sourceBody679_231 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_206 sourceBody679_230

def sourceBody679_232 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_205 sourceBody679_231

def sourceBody679_233 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_204 sourceBody679_232

def sourceBody679_234 : WordLangProgHOL (BitVec 64) :=
.call (some (([46]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody679_0, 679, 36)) (some 676) ([32, 60]) (some (32, sourceBody679_198, 679, 37))

def sourceBody679_235 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_234 sourceBody679_6

def sourceBody679_236 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_235 sourceBody679_0

def sourceBody679_237 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_212 sourceBody679_236

def sourceBody679_238 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_211 sourceBody679_237

def sourceBody679_239 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_238

def sourceBody679_240 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_239

def sourceBody679_241 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_233 sourceBody679_240

def sourceBody679_242 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_241 sourceBody679_224

def sourceBody679_243 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_196 sourceBody679_242

def sourceBody679_244 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_243

def sourceBody679_245 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_244

def sourceBody679_246 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 60 (Flapjack.WordRegImm.imm 0#64) sourceBody679_245 sourceBody679_0

def sourceBody679_247 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_246 sourceBody679_6

def sourceBody679_248 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_247 sourceBody679_0

def sourceBody679_249 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_186 sourceBody679_248

def sourceBody679_250 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_185 sourceBody679_249

def sourceBody679_251 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_181 sourceBody679_250

def sourceBody679_252 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_180 sourceBody679_251

def sourceBody679_253 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 44)

def sourceBody679_254 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody679_0, 679, 38)) (some 68) ([46]) (some (46, sourceBody679_190, 679, 39))

def sourceBody679_255 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_254 sourceBody679_6

def sourceBody679_256 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_255 sourceBody679_0

def sourceBody679_257 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_253 sourceBody679_256

def sourceBody679_258 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 44)

def sourceBody679_259 : WordLangProgHOL (BitVec 64) :=
.call (some (([46]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody679_0, 679, 40)) (some 68) ([32]) (some (32, sourceBody679_198, 679, 41))

def sourceBody679_260 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_259 sourceBody679_6

def sourceBody679_261 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_260 sourceBody679_0

def sourceBody679_262 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_258 sourceBody679_261

def sourceBody679_263 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 60 (Flapjack.WordLangExpHOL.var 44)

def sourceBody679_264 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 60

def sourceBody679_265 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody679_0, 679, 42)) (some 68) ([60]) (some (60, sourceBody679_264, 679, 43))

def sourceBody679_266 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_265 sourceBody679_6

def sourceBody679_267 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_266 sourceBody679_0

def sourceBody679_268 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_263 sourceBody679_267

def sourceBody679_269 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 44)

def sourceBody679_270 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody679_271 : WordLangProgHOL (BitVec 64) :=
.call (some (([60]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody679_0, 679, 44)) (some 68) ([16]) (some (16, sourceBody679_270, 679, 45))

def sourceBody679_272 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_271 sourceBody679_6

def sourceBody679_273 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_272 sourceBody679_0

def sourceBody679_274 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_269 sourceBody679_273

def sourceBody679_275 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 44)

def sourceBody679_276 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 42

def sourceBody679_277 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          Flapjack.Spt.ln)
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody679_0, 679, 46)) (some 68) ([42]) (some (42, sourceBody679_276, 679, 47))

def sourceBody679_278 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_277 sourceBody679_6

def sourceBody679_279 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_278 sourceBody679_0

def sourceBody679_280 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_275 sourceBody679_279

def sourceBody679_281 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 44)

def sourceBody679_282 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 28

def sourceBody679_283 : WordLangProgHOL (BitVec 64) :=
.call (some (([42]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          Flapjack.Spt.ln)
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody679_0, 679, 48)) (some 68) ([28]) (some (28, sourceBody679_282, 679, 49))

def sourceBody679_284 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_283 sourceBody679_6

def sourceBody679_285 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_284 sourceBody679_0

def sourceBody679_286 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_281 sourceBody679_285

def sourceBody679_287 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 56 (Flapjack.WordLangExpHOL.var 44)

def sourceBody679_288 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 56

def sourceBody679_289 : WordLangProgHOL (BitVec 64) :=
.call (some (([28]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          Flapjack.Spt.ln)
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody679_0, 679, 50)) (some 68) ([56]) (some (56, sourceBody679_288, 679, 51))

def sourceBody679_290 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_289 sourceBody679_6

def sourceBody679_291 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_290 sourceBody679_0

def sourceBody679_292 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_287 sourceBody679_291

def sourceBody679_293 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 44)

def sourceBody679_294 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 22

def sourceBody679_295 : WordLangProgHOL (BitVec 64) :=
.call (some (([56]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          PUnit.unit Flapjack.Spt.ln)
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody679_0, 679, 52)) (some 68) ([22]) (some (22, sourceBody679_294, 679, 53))

def sourceBody679_296 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_295 sourceBody679_6

def sourceBody679_297 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_296 sourceBody679_0

def sourceBody679_298 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_293 sourceBody679_297

def sourceBody679_299 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 2)

def sourceBody679_300 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 18)

def sourceBody679_301 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 64 (Flapjack.WordLangExpHOL.var 62)

def sourceBody679_302 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 12)

def sourceBody679_303 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 50

def sourceBody679_304 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          PUnit.unit Flapjack.Spt.ln)
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody679_0, 679, 54)) (some 669) ([50, 36, 64, 10]) (some (50, sourceBody679_303, 679, 55))

def sourceBody679_305 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_304 sourceBody679_6

def sourceBody679_306 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_305 sourceBody679_0

def sourceBody679_307 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_302 sourceBody679_306

def sourceBody679_308 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_301 sourceBody679_307

def sourceBody679_309 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_300 sourceBody679_308

def sourceBody679_310 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_299 sourceBody679_309

def sourceBody679_311 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_310

def sourceBody679_312 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_311

def sourceBody679_313 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 46)

def sourceBody679_314 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 64 (Flapjack.WordLangExpHOL.var 38)

def sourceBody679_315 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 24)

def sourceBody679_316 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          PUnit.unit Flapjack.Spt.ln)
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody679_0, 679, 56)) (some 669) ([50, 36, 64, 10]) (some (50, sourceBody679_303, 679, 57))

def sourceBody679_317 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_316 sourceBody679_6

def sourceBody679_318 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_317 sourceBody679_0

def sourceBody679_319 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_315 sourceBody679_318

def sourceBody679_320 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_314 sourceBody679_319

def sourceBody679_321 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_313 sourceBody679_320

def sourceBody679_322 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_299 sourceBody679_321

def sourceBody679_323 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_322

def sourceBody679_324 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_323

def sourceBody679_325 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_312 sourceBody679_324

def sourceBody679_326 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 32)

def sourceBody679_327 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 64 (Flapjack.WordLangExpHOL.var 46)

def sourceBody679_328 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          PUnit.unit Flapjack.Spt.ln)
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody679_0, 679, 58)) (some 667) ([50, 36, 64]) (some (50, sourceBody679_303, 679, 59))

def sourceBody679_329 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_328 sourceBody679_6

def sourceBody679_330 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_329 sourceBody679_0

def sourceBody679_331 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_327 sourceBody679_330

def sourceBody679_332 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_326 sourceBody679_331

def sourceBody679_333 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_299 sourceBody679_332

def sourceBody679_334 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_333

def sourceBody679_335 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_334

def sourceBody679_336 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_325 sourceBody679_335

def sourceBody679_337 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 60)

def sourceBody679_338 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 64 (Flapjack.WordLangExpHOL.var 32)

def sourceBody679_339 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          PUnit.unit Flapjack.Spt.ln)
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody679_0, 679, 60)) (some 666) ([50, 36, 64, 10]) (some (50, sourceBody679_303, 679, 61))

def sourceBody679_340 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_339 sourceBody679_6

def sourceBody679_341 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_340 sourceBody679_0

def sourceBody679_342 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_315 sourceBody679_341

def sourceBody679_343 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_338 sourceBody679_342

def sourceBody679_344 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_337 sourceBody679_343

def sourceBody679_345 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_299 sourceBody679_344

def sourceBody679_346 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_345

def sourceBody679_347 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_346

def sourceBody679_348 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_336 sourceBody679_347

def sourceBody679_349 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 16)

def sourceBody679_350 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 32)

def sourceBody679_351 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          PUnit.unit Flapjack.Spt.ln)
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody679_0, 679, 62)) (some 666) ([50, 36, 64, 10]) (some (50, sourceBody679_303, 679, 63))

def sourceBody679_352 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_351 sourceBody679_6

def sourceBody679_353 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_352 sourceBody679_0

def sourceBody679_354 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_350 sourceBody679_353

def sourceBody679_355 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_327 sourceBody679_354

def sourceBody679_356 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_349 sourceBody679_355

def sourceBody679_357 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_299 sourceBody679_356

def sourceBody679_358 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_357

def sourceBody679_359 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_358

def sourceBody679_360 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_348 sourceBody679_359

def sourceBody679_361 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 42)

def sourceBody679_362 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 64 (Flapjack.WordLangExpHOL.var 54)

def sourceBody679_363 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 34)

def sourceBody679_364 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          Flapjack.Spt.ln)
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          PUnit.unit Flapjack.Spt.ln)
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody679_0, 679, 64)) (some 666) ([50, 36, 64, 10]) (some (50, sourceBody679_303, 679, 65))

def sourceBody679_365 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_364 sourceBody679_6

def sourceBody679_366 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_365 sourceBody679_0

def sourceBody679_367 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_363 sourceBody679_366

def sourceBody679_368 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_362 sourceBody679_367

def sourceBody679_369 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_361 sourceBody679_368

def sourceBody679_370 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_299 sourceBody679_369

def sourceBody679_371 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_370

def sourceBody679_372 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_371

def sourceBody679_373 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_360 sourceBody679_372

def sourceBody679_374 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 28)

def sourceBody679_375 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 64 (Flapjack.WordLangExpHOL.var 18)

def sourceBody679_376 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          Flapjack.Spt.ln)
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          PUnit.unit Flapjack.Spt.ln)
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody679_0, 679, 66)) (some 667) ([50, 36, 64]) (some (50, sourceBody679_303, 679, 67))

def sourceBody679_377 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_376 sourceBody679_6

def sourceBody679_378 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_377 sourceBody679_0

def sourceBody679_379 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_375 sourceBody679_378

def sourceBody679_380 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_374 sourceBody679_379

def sourceBody679_381 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_299 sourceBody679_380

def sourceBody679_382 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_381

def sourceBody679_383 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_382

def sourceBody679_384 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_373 sourceBody679_383

def sourceBody679_385 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 64 (Flapjack.WordLangExpHOL.var 28)

def sourceBody679_386 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 42)

def sourceBody679_387 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          Flapjack.Spt.ln)
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          PUnit.unit Flapjack.Spt.ln)
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody679_0, 679, 68)) (some 666) ([50, 36, 64, 10]) (some (50, sourceBody679_303, 679, 69))

def sourceBody679_388 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_387 sourceBody679_6

def sourceBody679_389 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_388 sourceBody679_0

def sourceBody679_390 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_386 sourceBody679_389

def sourceBody679_391 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_385 sourceBody679_390

def sourceBody679_392 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_374 sourceBody679_391

def sourceBody679_393 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_299 sourceBody679_392

def sourceBody679_394 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_393

def sourceBody679_395 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_394

def sourceBody679_396 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_384 sourceBody679_395

def sourceBody679_397 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 16)

def sourceBody679_398 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          Flapjack.Spt.ln)
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          PUnit.unit Flapjack.Spt.ln)
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody679_0, 679, 70)) (some 669) ([50, 36, 64, 10]) (some (50, sourceBody679_303, 679, 71))

def sourceBody679_399 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_398 sourceBody679_6

def sourceBody679_400 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_399 sourceBody679_0

def sourceBody679_401 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_397 sourceBody679_400

def sourceBody679_402 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_385 sourceBody679_401

def sourceBody679_403 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_374 sourceBody679_402

def sourceBody679_404 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_299 sourceBody679_403

def sourceBody679_405 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_404

def sourceBody679_406 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_405

def sourceBody679_407 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_396 sourceBody679_406

def sourceBody679_408 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 56)

def sourceBody679_409 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 64 (Flapjack.WordLangExpHOL.var 60)

def sourceBody679_410 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 2#64)

def sourceBody679_411 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          Flapjack.Spt.ln)
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          PUnit.unit Flapjack.Spt.ln)
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody679_0, 679, 72)) (some 671) ([50, 36, 64, 10]) (some (50, sourceBody679_303, 679, 73))

def sourceBody679_412 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_411 sourceBody679_6

def sourceBody679_413 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_412 sourceBody679_0

def sourceBody679_414 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_410 sourceBody679_413

def sourceBody679_415 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_409 sourceBody679_414

def sourceBody679_416 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_408 sourceBody679_415

def sourceBody679_417 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_299 sourceBody679_416

def sourceBody679_418 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_417

def sourceBody679_419 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_418

def sourceBody679_420 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_407 sourceBody679_419

def sourceBody679_421 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 56)

def sourceBody679_422 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          Flapjack.Spt.ln)
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          PUnit.unit Flapjack.Spt.ln)
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody679_0, 679, 74)) (some 669) ([50, 36, 64, 10]) (some (50, sourceBody679_303, 679, 75))

def sourceBody679_423 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_422 sourceBody679_6

def sourceBody679_424 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_423 sourceBody679_0

def sourceBody679_425 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_421 sourceBody679_424

def sourceBody679_426 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_385 sourceBody679_425

def sourceBody679_427 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_374 sourceBody679_426

def sourceBody679_428 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_299 sourceBody679_427

def sourceBody679_429 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_428

def sourceBody679_430 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_429

def sourceBody679_431 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_420 sourceBody679_430

def sourceBody679_432 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 28)

def sourceBody679_433 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          Flapjack.Spt.ln)
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit))
          PUnit.unit Flapjack.Spt.ln)
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody679_0, 679, 76)) (some 666) ([50, 36, 64, 10]) (some (50, sourceBody679_303, 679, 77))

def sourceBody679_434 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_433 sourceBody679_6

def sourceBody679_435 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_434 sourceBody679_0

def sourceBody679_436 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_432 sourceBody679_435

def sourceBody679_437 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_327 sourceBody679_436

def sourceBody679_438 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_408 sourceBody679_437

def sourceBody679_439 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_299 sourceBody679_438

def sourceBody679_440 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_439

def sourceBody679_441 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_440

def sourceBody679_442 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_431 sourceBody679_441

def sourceBody679_443 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          Flapjack.Spt.ln)
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody679_0, 679, 78)) (some 669) ([50, 36, 64, 10]) (some (50, sourceBody679_303, 679, 79))

def sourceBody679_444 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_443 sourceBody679_6

def sourceBody679_445 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_444 sourceBody679_0

def sourceBody679_446 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_432 sourceBody679_445

def sourceBody679_447 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_409 sourceBody679_446

def sourceBody679_448 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_313 sourceBody679_447

def sourceBody679_449 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_299 sourceBody679_448

def sourceBody679_450 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_449

def sourceBody679_451 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_450

def sourceBody679_452 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_442 sourceBody679_451

def sourceBody679_453 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 46)

def sourceBody679_454 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          Flapjack.Spt.ln)
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody679_0, 679, 80)) (some 666) ([50, 36, 64, 10]) (some (50, sourceBody679_303, 679, 81))

def sourceBody679_455 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_454 sourceBody679_6

def sourceBody679_456 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_455 sourceBody679_0

def sourceBody679_457 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_453 sourceBody679_456

def sourceBody679_458 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_375 sourceBody679_457

def sourceBody679_459 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_313 sourceBody679_458

def sourceBody679_460 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_299 sourceBody679_459

def sourceBody679_461 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_460

def sourceBody679_462 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_461

def sourceBody679_463 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_452 sourceBody679_462

def sourceBody679_464 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 62)

def sourceBody679_465 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 64 (Flapjack.WordLangExpHOL.var 16)

def sourceBody679_466 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
          Flapjack.Spt.ln)
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody679_0, 679, 82)) (some 666) ([50, 36, 64, 10]) (some (50, sourceBody679_303, 679, 83))

def sourceBody679_467 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_466 sourceBody679_6

def sourceBody679_468 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_467 sourceBody679_0

def sourceBody679_469 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_302 sourceBody679_468

def sourceBody679_470 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_465 sourceBody679_469

def sourceBody679_471 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_464 sourceBody679_470

def sourceBody679_472 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_299 sourceBody679_471

def sourceBody679_473 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_472

def sourceBody679_474 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_473

def sourceBody679_475 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_463 sourceBody679_474

def sourceBody679_476 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 62)

def sourceBody679_477 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody679_0, 679, 84)) (some 669) ([50, 36, 64, 10]) (some (50, sourceBody679_303, 679, 85))

def sourceBody679_478 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_477 sourceBody679_6

def sourceBody679_479 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_478 sourceBody679_0

def sourceBody679_480 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_476 sourceBody679_479

def sourceBody679_481 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_327 sourceBody679_480

def sourceBody679_482 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_313 sourceBody679_481

def sourceBody679_483 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_299 sourceBody679_482

def sourceBody679_484 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_483

def sourceBody679_485 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_484

def sourceBody679_486 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_475 sourceBody679_485

def sourceBody679_487 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
        PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody679_0, 679, 86)) (some 666) ([50, 36, 64, 10]) (some (50, sourceBody679_303, 679, 87))

def sourceBody679_488 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_487 sourceBody679_6

def sourceBody679_489 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_488 sourceBody679_0

def sourceBody679_490 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_386 sourceBody679_489

def sourceBody679_491 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_465 sourceBody679_490

def sourceBody679_492 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_361 sourceBody679_491

def sourceBody679_493 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_299 sourceBody679_492

def sourceBody679_494 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_493

def sourceBody679_495 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_494

def sourceBody679_496 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_486 sourceBody679_495

def sourceBody679_497 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 4)

def sourceBody679_498 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 64 (Flapjack.WordLangExpHOL.var 44)

def sourceBody679_499 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
        PUnit.unit Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody679_0, 679, 88)) (some 77) ([50, 36, 64]) (some (50, sourceBody679_303, 679, 89))

def sourceBody679_500 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_499 sourceBody679_6

def sourceBody679_501 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_500 sourceBody679_0

def sourceBody679_502 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_498 sourceBody679_501

def sourceBody679_503 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_408 sourceBody679_502

def sourceBody679_504 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_497 sourceBody679_503

def sourceBody679_505 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_504

def sourceBody679_506 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_505

def sourceBody679_507 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_496 sourceBody679_506

def sourceBody679_508 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.var 44])

def sourceBody679_509 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
      (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
        PUnit.unit Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody679_0, 679, 90)) (some 77) ([50, 36, 64]) (some (50, sourceBody679_303, 679, 91))

def sourceBody679_510 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_509 sourceBody679_6

def sourceBody679_511 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_510 sourceBody679_0

def sourceBody679_512 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_498 sourceBody679_511

def sourceBody679_513 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_313 sourceBody679_512

def sourceBody679_514 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_508 sourceBody679_513

def sourceBody679_515 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_514

def sourceBody679_516 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_515

def sourceBody679_517 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_507 sourceBody679_516

def sourceBody679_518 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 4,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 44)
        (Flapjack.WordLangExpHOL.const 1#64)])

def sourceBody679_519 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody679_0, 679, 92)) (some 77) ([50, 36, 64]) (some (50, sourceBody679_303, 679, 93))

def sourceBody679_520 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_519 sourceBody679_6

def sourceBody679_521 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_520 sourceBody679_0

def sourceBody679_522 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_498 sourceBody679_521

def sourceBody679_523 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_361 sourceBody679_522

def sourceBody679_524 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_518 sourceBody679_523

def sourceBody679_525 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_524

def sourceBody679_526 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_525

def sourceBody679_527 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_517 sourceBody679_526

def sourceBody679_528 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 14)

def sourceBody679_529 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody679_0, 679, 94)) (some 70) ([50]) (some (50, sourceBody679_303, 679, 95))

def sourceBody679_530 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_529 sourceBody679_6

def sourceBody679_531 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_530 sourceBody679_0

def sourceBody679_532 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_528 sourceBody679_531

def sourceBody679_533 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_532

def sourceBody679_534 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_533

def sourceBody679_535 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_527 sourceBody679_534

def sourceBody679_536 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody679_537 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [22]

def sourceBody679_538 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_537 sourceBody679_0

def sourceBody679_539 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_536 sourceBody679_538

def sourceBody679_540 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_535 sourceBody679_539

def sourceBody679_541 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_298 sourceBody679_540

def sourceBody679_542 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_541

def sourceBody679_543 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_542

def sourceBody679_544 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_292 sourceBody679_543

def sourceBody679_545 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_544

def sourceBody679_546 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_545

def sourceBody679_547 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_286 sourceBody679_546

def sourceBody679_548 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_547

def sourceBody679_549 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_548

def sourceBody679_550 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_280 sourceBody679_549

def sourceBody679_551 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_550

def sourceBody679_552 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_551

def sourceBody679_553 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_274 sourceBody679_552

def sourceBody679_554 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_553

def sourceBody679_555 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_554

def sourceBody679_556 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_268 sourceBody679_555

def sourceBody679_557 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_556

def sourceBody679_558 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_557

def sourceBody679_559 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_262 sourceBody679_558

def sourceBody679_560 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_559

def sourceBody679_561 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_560

def sourceBody679_562 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_257 sourceBody679_561

def sourceBody679_563 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_562

def sourceBody679_564 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_563

def sourceBody679_565 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_252 sourceBody679_564

def sourceBody679_566 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_179 sourceBody679_565

def sourceBody679_567 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_566

def sourceBody679_568 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_567

def sourceBody679_569 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_172 sourceBody679_568

def sourceBody679_570 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_121 sourceBody679_569

def sourceBody679_571 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_570

def sourceBody679_572 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_571

def sourceBody679_573 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_115 sourceBody679_572

def sourceBody679_574 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_573

def sourceBody679_575 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_574

def sourceBody679_576 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_109 sourceBody679_575

def sourceBody679_577 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_576

def sourceBody679_578 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_577

def sourceBody679_579 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_103 sourceBody679_578

def sourceBody679_580 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_579

def sourceBody679_581 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_580

def sourceBody679_582 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_97 sourceBody679_581

def sourceBody679_583 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_582

def sourceBody679_584 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_96 sourceBody679_583

def sourceBody679_585 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_584

def sourceBody679_586 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_22 sourceBody679_585

def sourceBody679_587 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_586

def sourceBody679_588 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_95 sourceBody679_587

def sourceBody679_589 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_588

def sourceBody679_590 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_94 sourceBody679_589

def sourceBody679_591 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_590

def sourceBody679_592 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_93 sourceBody679_591

def sourceBody679_593 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_592

def sourceBody679_594 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_92 sourceBody679_593

def sourceBody679_595 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_594

def sourceBody679_596 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_595

def sourceBody679_597 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_89 sourceBody679_596

def sourceBody679_598 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_54 sourceBody679_597

def sourceBody679_599 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_598

def sourceBody679_600 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_599

def sourceBody679_601 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_47 sourceBody679_600

def sourceBody679_602 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_10 sourceBody679_601

def sourceBody679_603 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_602

def sourceBody679_604 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_603

def sourceBody679_605 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_1 sourceBody679_604

def sourceBody679_606 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody679_0 sourceBody679_605

def source679 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (679, 5, sourceBody679_606)
end InitECandidate.Proofs.WordStages
