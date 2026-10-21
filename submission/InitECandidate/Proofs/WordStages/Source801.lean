import InitECandidate.Proofs.WordStages.Source785
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody801_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 90 (Flapjack.WordLangExpHOL.var 2)

def sourceBody801_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.load8 90 (Flapjack.WordLangAddr.addr 90 0#64))

def sourceBody801_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody801_3 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_1 sourceBody801_2

def sourceBody801_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_0 sourceBody801_3

def sourceBody801_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 90)

def sourceBody801_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 76
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and
    [Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr (Flapjack.WordLangExpHOL.var 20)
        (Flapjack.WordLangExpHOL.const 7#64),
      Flapjack.WordLangExpHOL.const 1#64])

def sourceBody801_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 48
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and
    [Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr (Flapjack.WordLangExpHOL.var 20)
        (Flapjack.WordLangExpHOL.const 6#64),
      Flapjack.WordLangExpHOL.const 1#64])

def sourceBody801_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 106
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and
    [Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr (Flapjack.WordLangExpHOL.var 20)
        (Flapjack.WordLangExpHOL.const 5#64),
      Flapjack.WordLangExpHOL.const 1#64])

def sourceBody801_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 68 (Flapjack.WordLangExpHOL.var 76)

def sourceBody801_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody801_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 68 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody801_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 68 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody801_13 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 68 (Flapjack.WordRegImm.reg 40) sourceBody801_11 sourceBody801_12

def sourceBody801_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody801_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_13 sourceBody801_14

def sourceBody801_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 98 (Flapjack.WordLangExpHOL.var 68)

def sourceBody801_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody801_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [12]

def sourceBody801_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_18 sourceBody801_2

def sourceBody801_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_17 sourceBody801_19

def sourceBody801_21 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 98 (Flapjack.WordRegImm.imm 0#64) sourceBody801_20 sourceBody801_2

def sourceBody801_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_21 sourceBody801_14

def sourceBody801_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_22 sourceBody801_2

def sourceBody801_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_16 sourceBody801_23

def sourceBody801_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_15 sourceBody801_24

def sourceBody801_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_10 sourceBody801_25

def sourceBody801_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_9 sourceBody801_26

def sourceBody801_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 68

def sourceBody801_29 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
          Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody801_2, 801, 2)) (some 69) ([]) (some (68, sourceBody801_28, 801, 3))

def sourceBody801_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_29 sourceBody801_14

def sourceBody801_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_30 sourceBody801_2

def sourceBody801_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.const 48#64)

def sourceBody801_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 40

def sourceBody801_34 : WordLangProgHOL (BitVec 64) :=
.call (some (([68]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
          Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody801_2, 801, 4)) (some 68) ([40]) (some (40, sourceBody801_33, 801, 5))

def sourceBody801_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_34 sourceBody801_14

def sourceBody801_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_35 sourceBody801_2

def sourceBody801_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_32 sourceBody801_36

def sourceBody801_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 2)

def sourceBody801_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 84 (Flapjack.WordLangExpHOL.const 48#64)

def sourceBody801_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 98

def sourceBody801_41 : WordLangProgHOL (BitVec 64) :=
.call (some (([40]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
          Flapjack.Spt.ln))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
        PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody801_2, 801, 6)) (some 77) ([98, 28, 84]) (some (98, sourceBody801_40, 801, 7))

def sourceBody801_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_41 sourceBody801_14

def sourceBody801_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_42 sourceBody801_2

def sourceBody801_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_39 sourceBody801_43

def sourceBody801_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_38 sourceBody801_44

def sourceBody801_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_16 sourceBody801_45

def sourceBody801_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_46

def sourceBody801_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_47

def sourceBody801_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 68)

def sourceBody801_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 98
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and [Flapjack.WordLangExpHOL.var 20, Flapjack.WordLangExpHOL.const 31#64])

def sourceBody801_51 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.store8 98 (Flapjack.WordLangAddr.addr 40 0#64))

def sourceBody801_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_51 sourceBody801_2

def sourceBody801_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_50 sourceBody801_52

def sourceBody801_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_49 sourceBody801_53

def sourceBody801_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_48 sourceBody801_54

def sourceBody801_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 68)

def sourceBody801_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody801_58 : WordLangProgHOL (BitVec 64) :=
.call (some (([40, 98, 28, 84, 56, 114]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
          Flapjack.Spt.ln))
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody801_2, 801, 8)) (some 721) ([8]) (some (8, sourceBody801_57, 801, 9))

def sourceBody801_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_58 sourceBody801_14

def sourceBody801_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_59 sourceBody801_2

def sourceBody801_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_56 sourceBody801_60

def sourceBody801_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 64 (Flapjack.WordLangExpHOL.var 12)

def sourceBody801_63 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 64

def sourceBody801_64 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
          (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
            (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody801_2, 801, 10)) (some 70) ([64]) (some (64, sourceBody801_63, 801, 11))

def sourceBody801_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_64 sourceBody801_14

def sourceBody801_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_65 sourceBody801_2

def sourceBody801_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_62 sourceBody801_66

def sourceBody801_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_67

def sourceBody801_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_68

def sourceBody801_70 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 64 (Flapjack.WordLangExpHOL.var 48)

def sourceBody801_71 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody801_72 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 64 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody801_73 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 64 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody801_74 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 64 (Flapjack.WordRegImm.reg 36) sourceBody801_72 sourceBody801_73

def sourceBody801_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_74 sourceBody801_14

def sourceBody801_76 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 94 (Flapjack.WordLangExpHOL.var 64)

def sourceBody801_77 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 64 (Flapjack.WordLangExpHOL.var 40)

def sourceBody801_78 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 98)

def sourceBody801_79 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 94 (Flapjack.WordLangExpHOL.var 28)

def sourceBody801_80 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 84)

def sourceBody801_81 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 80 (Flapjack.WordLangExpHOL.var 56)

def sourceBody801_82 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.var 114)

def sourceBody801_83 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
          Flapjack.Spt.ln))
      (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody801_2, 801, 12)) (some 701) ([64, 36, 94, 24, 80, 52]) (some (64, sourceBody801_63, 801, 13))

def sourceBody801_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_83 sourceBody801_14

def sourceBody801_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_84 sourceBody801_2

def sourceBody801_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_82 sourceBody801_85

def sourceBody801_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_81 sourceBody801_86

def sourceBody801_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_80 sourceBody801_87

def sourceBody801_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_79 sourceBody801_88

def sourceBody801_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_78 sourceBody801_89

def sourceBody801_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_77 sourceBody801_90

def sourceBody801_92 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 8)

def sourceBody801_93 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 94 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody801_94 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody801_95 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 36 (Flapjack.WordRegImm.reg 94) sourceBody801_71 sourceBody801_94

def sourceBody801_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_95 sourceBody801_14

def sourceBody801_97 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 80 (Flapjack.WordLangExpHOL.var 106)

def sourceBody801_98 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 52 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody801_99 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 80 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody801_100 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 80 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody801_101 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 80 (Flapjack.WordRegImm.reg 52) sourceBody801_99 sourceBody801_100

def sourceBody801_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_101 sourceBody801_14

def sourceBody801_103 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody801_104 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 72
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.or [Flapjack.WordLangExpHOL.var 36, Flapjack.WordLangExpHOL.var 80])

def sourceBody801_105 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody801_106 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 16 (Flapjack.WordRegImm.reg 72) sourceBody801_105 sourceBody801_103

def sourceBody801_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_106 sourceBody801_14

def sourceBody801_108 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 16)

def sourceBody801_109 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [64]

def sourceBody801_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_109 sourceBody801_2

def sourceBody801_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_73 sourceBody801_110

def sourceBody801_112 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 44 (Flapjack.WordRegImm.imm 0#64) sourceBody801_111 sourceBody801_2

def sourceBody801_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_112 sourceBody801_14

def sourceBody801_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_113 sourceBody801_2

def sourceBody801_115 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_108 sourceBody801_114

def sourceBody801_116 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_107 sourceBody801_115

def sourceBody801_117 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_104 sourceBody801_116

def sourceBody801_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_103 sourceBody801_117

def sourceBody801_119 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_102 sourceBody801_118

def sourceBody801_120 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_98 sourceBody801_119

def sourceBody801_121 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_97 sourceBody801_120

def sourceBody801_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_96 sourceBody801_121

def sourceBody801_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_93 sourceBody801_122

def sourceBody801_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_92 sourceBody801_123

def sourceBody801_125 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 4)

def sourceBody801_126 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 36

def sourceBody801_127 : WordLangProgHOL (BitVec 64) :=
.call (some (([64]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody801_2, 801, 14)) (some 762) ([36]) (some (36, sourceBody801_126, 801, 15))

def sourceBody801_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_127 sourceBody801_14

def sourceBody801_129 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_128 sourceBody801_2

def sourceBody801_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_125 sourceBody801_129

def sourceBody801_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_130

def sourceBody801_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_131

def sourceBody801_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_124 sourceBody801_132

def sourceBody801_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_72 sourceBody801_110

def sourceBody801_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_133 sourceBody801_134

def sourceBody801_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_91 sourceBody801_135

def sourceBody801_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_136

def sourceBody801_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_137

def sourceBody801_139 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 94 (Flapjack.WordRegImm.imm 0#64) sourceBody801_138 sourceBody801_2

def sourceBody801_140 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_139 sourceBody801_14

def sourceBody801_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_140 sourceBody801_2

def sourceBody801_142 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_76 sourceBody801_141

def sourceBody801_143 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_75 sourceBody801_142

def sourceBody801_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_71 sourceBody801_143

def sourceBody801_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_70 sourceBody801_144

def sourceBody801_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_69 sourceBody801_145

def sourceBody801_147 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 110 (Flapjack.WordLangExpHOL.const 13402431016077863595#64)

def sourceBody801_148 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 2210141511517208575#64)

def sourceBody801_149 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 72 (Flapjack.WordLangExpHOL.const 7435674573564081700#64)

def sourceBody801_150 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.const 7239337960414712511#64)

def sourceBody801_151 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 102 (Flapjack.WordLangExpHOL.const 5412103778470702295#64)

def sourceBody801_152 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.const 1873798617647539866#64)

def sourceBody801_153 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
          (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
            (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody801_2, 801, 16)) (some 703) ([64, 36, 94, 24, 80, 52, 110, 16, 72, 44, 102, 32]) (some (64, sourceBody801_63, 801, 17))

def sourceBody801_154 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_153 sourceBody801_14

def sourceBody801_155 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_154 sourceBody801_2

def sourceBody801_156 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_152 sourceBody801_155

def sourceBody801_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_151 sourceBody801_156

def sourceBody801_158 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_150 sourceBody801_157

def sourceBody801_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_149 sourceBody801_158

def sourceBody801_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_148 sourceBody801_159

def sourceBody801_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_147 sourceBody801_160

def sourceBody801_162 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_82 sourceBody801_161

def sourceBody801_163 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_81 sourceBody801_162

def sourceBody801_164 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_80 sourceBody801_163

def sourceBody801_165 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_79 sourceBody801_164

def sourceBody801_166 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_78 sourceBody801_165

def sourceBody801_167 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_77 sourceBody801_166

def sourceBody801_168 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 36)

def sourceBody801_169 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 24 (Flapjack.WordRegImm.imm 0#64) sourceBody801_111 sourceBody801_2

def sourceBody801_170 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_169 sourceBody801_14

def sourceBody801_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_170 sourceBody801_2

def sourceBody801_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_168 sourceBody801_171

def sourceBody801_173 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_96 sourceBody801_172

def sourceBody801_174 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_93 sourceBody801_173

def sourceBody801_175 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_92 sourceBody801_174

def sourceBody801_176 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 110 (Flapjack.WordLangExpHOL.var 40)

def sourceBody801_177 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 98)

def sourceBody801_178 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 72 (Flapjack.WordLangExpHOL.var 28)

def sourceBody801_179 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 84)

def sourceBody801_180 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 102 (Flapjack.WordLangExpHOL.var 56)

def sourceBody801_181 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 114)

def sourceBody801_182 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 110

def sourceBody801_183 : WordLangProgHOL (BitVec 64) :=
.call (some (([64, 36, 94, 24, 80, 52]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn Flapjack.Spt.ln
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
          Flapjack.Spt.ln))
      (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody801_2, 801, 18)) (some 712) ([110, 16, 72, 44, 102, 32]) (some (110, sourceBody801_182, 801, 19))

def sourceBody801_184 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_183 sourceBody801_14

def sourceBody801_185 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_184 sourceBody801_2

def sourceBody801_186 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_181 sourceBody801_185

def sourceBody801_187 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_180 sourceBody801_186

def sourceBody801_188 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_179 sourceBody801_187

def sourceBody801_189 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_178 sourceBody801_188

def sourceBody801_190 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_177 sourceBody801_189

def sourceBody801_191 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_176 sourceBody801_190

def sourceBody801_192 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 88 (Flapjack.WordLangExpHOL.var 64)

def sourceBody801_193 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 60 (Flapjack.WordLangExpHOL.var 36)

def sourceBody801_194 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 118 (Flapjack.WordLangExpHOL.var 94)

def sourceBody801_195 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 24)

def sourceBody801_196 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 62 (Flapjack.WordLangExpHOL.var 80)

def sourceBody801_197 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 52)

def sourceBody801_198 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 88

def sourceBody801_199 : WordLangProgHOL (BitVec 64) :=
.call (some (([110, 16, 72, 44, 102, 32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
          Flapjack.Spt.ln)
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
          Flapjack.Spt.ln))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody801_2, 801, 20)) (some 711) ([88, 60, 118, 6, 62, 34]) (some (88, sourceBody801_198, 801, 21))

def sourceBody801_200 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_199 sourceBody801_14

def sourceBody801_201 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_200 sourceBody801_2

def sourceBody801_202 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_197 sourceBody801_201

def sourceBody801_203 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_196 sourceBody801_202

def sourceBody801_204 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_195 sourceBody801_203

def sourceBody801_205 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_194 sourceBody801_204

def sourceBody801_206 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_193 sourceBody801_205

def sourceBody801_207 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_192 sourceBody801_206

def sourceBody801_208 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 88 (Flapjack.WordLangExpHOL.var 110)

def sourceBody801_209 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 60 (Flapjack.WordLangExpHOL.var 16)

def sourceBody801_210 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 118 (Flapjack.WordLangExpHOL.var 72)

def sourceBody801_211 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 44)

def sourceBody801_212 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 62 (Flapjack.WordLangExpHOL.var 102)

def sourceBody801_213 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.var 32)

def sourceBody801_214 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 92 (Flapjack.WordLangExpHOL.var 64)

def sourceBody801_215 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 36)

def sourceBody801_216 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 78 (Flapjack.WordLangExpHOL.var 94)

def sourceBody801_217 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 24)

def sourceBody801_218 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 108 (Flapjack.WordLangExpHOL.var 80)

def sourceBody801_219 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 52)

def sourceBody801_220 : WordLangProgHOL (BitVec 64) :=
.call (some (([110, 16, 72, 44, 102, 32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
          Flapjack.Spt.ln)
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
          Flapjack.Spt.ln))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody801_2, 801, 22)) (some 710) ([88, 60, 118, 6, 62, 34, 92, 22, 78, 50, 108, 14]) (some (88, sourceBody801_198, 801, 23))

def sourceBody801_221 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_220 sourceBody801_14

def sourceBody801_222 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_221 sourceBody801_2

def sourceBody801_223 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_219 sourceBody801_222

def sourceBody801_224 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_218 sourceBody801_223

def sourceBody801_225 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_217 sourceBody801_224

def sourceBody801_226 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_216 sourceBody801_225

def sourceBody801_227 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_215 sourceBody801_226

def sourceBody801_228 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_214 sourceBody801_227

def sourceBody801_229 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_213 sourceBody801_228

def sourceBody801_230 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_212 sourceBody801_229

def sourceBody801_231 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_211 sourceBody801_230

def sourceBody801_232 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_210 sourceBody801_231

def sourceBody801_233 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_209 sourceBody801_232

def sourceBody801_234 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_208 sourceBody801_233

def sourceBody801_235 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 88
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.load
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
            [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                  Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                    (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                    (Flapjack.WordLangExpHOL.const 1#64)],
              Flapjack.WordLangExpHOL.const 392#64]),
        Flapjack.WordLangExpHOL.const 240#64]))

def sourceBody801_236 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 60
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.load
              (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
                [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                    [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                        (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                        (Flapjack.WordLangExpHOL.const 1#64)],
                  Flapjack.WordLangExpHOL.const 392#64]),
            Flapjack.WordLangExpHOL.const 240#64],
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody801_237 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 118
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.load
              (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
                [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                    [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                        (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                        (Flapjack.WordLangExpHOL.const 1#64)],
                  Flapjack.WordLangExpHOL.const 392#64]),
            Flapjack.WordLangExpHOL.const 240#64],
        Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody801_238 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.load
              (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
                [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                    [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                        (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                        (Flapjack.WordLangExpHOL.const 1#64)],
                  Flapjack.WordLangExpHOL.const 392#64]),
            Flapjack.WordLangExpHOL.const 240#64],
        Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody801_239 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 62
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.load
              (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
                [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                    [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                        (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                        (Flapjack.WordLangExpHOL.const 1#64)],
                  Flapjack.WordLangExpHOL.const 392#64]),
            Flapjack.WordLangExpHOL.const 240#64],
        Flapjack.WordLangExpHOL.const 32#64]))

def sourceBody801_240 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.load
              (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
                [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
                    [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                        (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength)
                        (Flapjack.WordLangExpHOL.const 1#64)],
                  Flapjack.WordLangExpHOL.const 392#64]),
            Flapjack.WordLangExpHOL.const 240#64],
        Flapjack.WordLangExpHOL.const 40#64]))

def sourceBody801_241 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 92 (Flapjack.WordLangExpHOL.var 110)

def sourceBody801_242 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 16)

def sourceBody801_243 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 78 (Flapjack.WordLangExpHOL.var 72)

def sourceBody801_244 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 50 (Flapjack.WordLangExpHOL.var 44)

def sourceBody801_245 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 108 (Flapjack.WordLangExpHOL.var 102)

def sourceBody801_246 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 32)

def sourceBody801_247 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 70 (Flapjack.WordLangExpHOL.var 88)

def sourceBody801_248 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 60)

def sourceBody801_249 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 100 (Flapjack.WordLangExpHOL.var 118)

def sourceBody801_250 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 6)

def sourceBody801_251 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 86 (Flapjack.WordLangExpHOL.var 62)

def sourceBody801_252 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.var 34)

def sourceBody801_253 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 92

def sourceBody801_254 : WordLangProgHOL (BitVec 64) :=
.call (some (([110, 16, 72, 44, 102, 32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
          Flapjack.Spt.ln)
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
          Flapjack.Spt.ln))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody801_2, 801, 24)) (some 706) ([92, 22, 78, 50, 108, 14, 70, 42, 100, 30, 86, 58]) (some (92, sourceBody801_253, 801, 25))

def sourceBody801_255 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_254 sourceBody801_14

def sourceBody801_256 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_255 sourceBody801_2

def sourceBody801_257 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_252 sourceBody801_256

def sourceBody801_258 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_251 sourceBody801_257

def sourceBody801_259 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_250 sourceBody801_258

def sourceBody801_260 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_249 sourceBody801_259

def sourceBody801_261 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_248 sourceBody801_260

def sourceBody801_262 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_247 sourceBody801_261

def sourceBody801_263 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_246 sourceBody801_262

def sourceBody801_264 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_245 sourceBody801_263

def sourceBody801_265 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_244 sourceBody801_264

def sourceBody801_266 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_243 sourceBody801_265

def sourceBody801_267 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_242 sourceBody801_266

def sourceBody801_268 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_241 sourceBody801_267

def sourceBody801_269 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 70 (Flapjack.WordLangExpHOL.var 110)

def sourceBody801_270 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 16)

def sourceBody801_271 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 100 (Flapjack.WordLangExpHOL.var 72)

def sourceBody801_272 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 44)

def sourceBody801_273 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 86 (Flapjack.WordLangExpHOL.var 102)

def sourceBody801_274 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 58 (Flapjack.WordLangExpHOL.var 32)

def sourceBody801_275 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 116
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub
          [Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
              [Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.currHeap,
                Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                  (Flapjack.WordLangExpHOL.lookup Flapjack.WordStore.heapLength) (Flapjack.WordLangExpHOL.const 1#64)],
            Flapjack.WordLangExpHOL.const 392#64]),
      Flapjack.WordLangExpHOL.const 1432#64])

def sourceBody801_276 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 6#64)

def sourceBody801_277 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 70

def sourceBody801_278 : WordLangProgHOL (BitVec 64) :=
.call (some (([92, 22, 78, 50, 108, 14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
            (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
          Flapjack.Spt.ln))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
          (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
            (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody801_2, 801, 26)) (some 718) ([70, 42, 100, 30, 86, 58, 116, 10]) (some (70, sourceBody801_277, 801, 27))

def sourceBody801_279 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_278 sourceBody801_14

def sourceBody801_280 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_279 sourceBody801_2

def sourceBody801_281 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_276 sourceBody801_280

def sourceBody801_282 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_275 sourceBody801_281

def sourceBody801_283 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_274 sourceBody801_282

def sourceBody801_284 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_273 sourceBody801_283

def sourceBody801_285 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_272 sourceBody801_284

def sourceBody801_286 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_271 sourceBody801_285

def sourceBody801_287 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_270 sourceBody801_286

def sourceBody801_288 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_269 sourceBody801_287

def sourceBody801_289 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 116 (Flapjack.WordLangExpHOL.var 92)

def sourceBody801_290 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 22)

def sourceBody801_291 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 66 (Flapjack.WordLangExpHOL.var 78)

def sourceBody801_292 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 50)

def sourceBody801_293 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 96 (Flapjack.WordLangExpHOL.var 108)

def sourceBody801_294 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 14)

def sourceBody801_295 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 116

def sourceBody801_296 : WordLangProgHOL (BitVec 64) :=
.call (some (([70, 42, 100, 30, 86, 58]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
            (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
          PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
            (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
          (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
            (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody801_2, 801, 28)) (some 711) ([116, 10, 66, 38, 96, 26]) (some (116, sourceBody801_295, 801, 29))

def sourceBody801_297 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_296 sourceBody801_14

def sourceBody801_298 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_297 sourceBody801_2

def sourceBody801_299 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_294 sourceBody801_298

def sourceBody801_300 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_293 sourceBody801_299

def sourceBody801_301 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_292 sourceBody801_300

def sourceBody801_302 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_291 sourceBody801_301

def sourceBody801_303 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_290 sourceBody801_302

def sourceBody801_304 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_289 sourceBody801_303

def sourceBody801_305 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 70)

def sourceBody801_306 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 66 (Flapjack.WordLangExpHOL.var 42)

def sourceBody801_307 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 100)

def sourceBody801_308 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 96 (Flapjack.WordLangExpHOL.var 30)

def sourceBody801_309 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 86)

def sourceBody801_310 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 82 (Flapjack.WordLangExpHOL.var 58)

def sourceBody801_311 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 110)

def sourceBody801_312 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 112 (Flapjack.WordLangExpHOL.var 16)

def sourceBody801_313 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 72)

def sourceBody801_314 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 74 (Flapjack.WordLangExpHOL.var 44)

def sourceBody801_315 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 46 (Flapjack.WordLangExpHOL.var 102)

def sourceBody801_316 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 104 (Flapjack.WordLangExpHOL.var 32)

def sourceBody801_317 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody801_318 : WordLangProgHOL (BitVec 64) :=
.call (some (([116]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
          PUnit.unit (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
            (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody801_2, 801, 30)) (some 702) ([10, 66, 38, 96, 26, 82, 54, 112, 18, 74, 46, 104]) (some (10, sourceBody801_317, 801, 31))

def sourceBody801_319 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_318 sourceBody801_14

def sourceBody801_320 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_319 sourceBody801_2

def sourceBody801_321 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_316 sourceBody801_320

def sourceBody801_322 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_315 sourceBody801_321

def sourceBody801_323 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_314 sourceBody801_322

def sourceBody801_324 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_313 sourceBody801_323

def sourceBody801_325 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_312 sourceBody801_324

def sourceBody801_326 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_311 sourceBody801_325

def sourceBody801_327 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_310 sourceBody801_326

def sourceBody801_328 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_309 sourceBody801_327

def sourceBody801_329 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_308 sourceBody801_328

def sourceBody801_330 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_307 sourceBody801_329

def sourceBody801_331 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_306 sourceBody801_330

def sourceBody801_332 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_305 sourceBody801_331

def sourceBody801_333 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 66 (Flapjack.WordLangExpHOL.var 116)

def sourceBody801_334 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody801_335 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 66 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody801_336 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 66 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody801_337 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 66 (Flapjack.WordRegImm.reg 38) sourceBody801_335 sourceBody801_336

def sourceBody801_338 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_337 sourceBody801_14

def sourceBody801_339 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 96 (Flapjack.WordLangExpHOL.var 66)

def sourceBody801_340 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody801_341 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [10]

def sourceBody801_342 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_341 sourceBody801_2

def sourceBody801_343 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_340 sourceBody801_342

def sourceBody801_344 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 96 (Flapjack.WordRegImm.imm 0#64) sourceBody801_343 sourceBody801_2

def sourceBody801_345 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_344 sourceBody801_14

def sourceBody801_346 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_345 sourceBody801_2

def sourceBody801_347 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_339 sourceBody801_346

def sourceBody801_348 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_338 sourceBody801_347

def sourceBody801_349 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_334 sourceBody801_348

def sourceBody801_350 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_333 sourceBody801_349

def sourceBody801_351 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 66 (Flapjack.WordLangExpHOL.var 92)

def sourceBody801_352 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 22)

def sourceBody801_353 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 96 (Flapjack.WordLangExpHOL.var 78)

def sourceBody801_354 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 50)

def sourceBody801_355 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 82 (Flapjack.WordLangExpHOL.var 108)

def sourceBody801_356 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 14)

def sourceBody801_357 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 66

def sourceBody801_358 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bs
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
          PUnit.unit (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)))
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
            (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
          (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody801_2, 801, 32)) (some 720) ([66, 38, 96, 26, 82, 54]) (some (66, sourceBody801_357, 801, 33))

def sourceBody801_359 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_358 sourceBody801_14

def sourceBody801_360 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_359 sourceBody801_2

def sourceBody801_361 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_356 sourceBody801_360

def sourceBody801_362 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_355 sourceBody801_361

def sourceBody801_363 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_354 sourceBody801_362

def sourceBody801_364 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_353 sourceBody801_363

def sourceBody801_365 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_352 sourceBody801_364

def sourceBody801_366 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_351 sourceBody801_365

def sourceBody801_367 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 10)

def sourceBody801_368 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 96 (Flapjack.WordLangExpHOL.var 106)

def sourceBody801_369 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody801_370 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 38 (Flapjack.WordRegImm.reg 96) sourceBody801_369 sourceBody801_334

def sourceBody801_371 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_370 sourceBody801_14

def sourceBody801_372 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 38)

def sourceBody801_373 : WordLangProgHOL (BitVec 64) :=
.call (some (([92, 22, 78, 50, 108, 14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn
        (Flapjack.Spt.bn
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
          Flapjack.Spt.ln)
        Flapjack.Spt.ln)
      (Flapjack.Spt.bs
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
          (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
            (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody801_2, 801, 34)) (some 708) ([66, 38, 96, 26, 82, 54]) (some (66, sourceBody801_357, 801, 35))

def sourceBody801_374 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_373 sourceBody801_14

def sourceBody801_375 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_374 sourceBody801_2

def sourceBody801_376 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_356 sourceBody801_375

def sourceBody801_377 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_355 sourceBody801_376

def sourceBody801_378 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_354 sourceBody801_377

def sourceBody801_379 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_353 sourceBody801_378

def sourceBody801_380 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_352 sourceBody801_379

def sourceBody801_381 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_351 sourceBody801_380

def sourceBody801_382 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 26 (Flapjack.WordRegImm.imm 0#64) sourceBody801_381 sourceBody801_2

def sourceBody801_383 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_382 sourceBody801_14

def sourceBody801_384 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_383 sourceBody801_2

def sourceBody801_385 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_372 sourceBody801_384

def sourceBody801_386 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_371 sourceBody801_385

def sourceBody801_387 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_368 sourceBody801_386

def sourceBody801_388 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_367 sourceBody801_387

def sourceBody801_389 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 66 (Flapjack.WordLangExpHOL.var 4)

def sourceBody801_390 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 64)

def sourceBody801_391 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 96 (Flapjack.WordLangExpHOL.var 36)

def sourceBody801_392 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 94)

def sourceBody801_393 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 82 (Flapjack.WordLangExpHOL.var 24)

def sourceBody801_394 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 80)

def sourceBody801_395 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 112 (Flapjack.WordLangExpHOL.var 52)

def sourceBody801_396 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 38)

def sourceBody801_397 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 66) 18

def sourceBody801_398 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_397 sourceBody801_2

def sourceBody801_399 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_396 sourceBody801_398

def sourceBody801_400 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 96)

def sourceBody801_401 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 66, Flapjack.WordLangExpHOL.const 8#64])
  18

def sourceBody801_402 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_401 sourceBody801_2

def sourceBody801_403 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_400 sourceBody801_402

def sourceBody801_404 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 26)

def sourceBody801_405 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 66, Flapjack.WordLangExpHOL.const 16#64])
  18

def sourceBody801_406 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_405 sourceBody801_2

def sourceBody801_407 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_404 sourceBody801_406

def sourceBody801_408 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 82)

def sourceBody801_409 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 66, Flapjack.WordLangExpHOL.const 24#64])
  18

def sourceBody801_410 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_409 sourceBody801_2

def sourceBody801_411 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_408 sourceBody801_410

def sourceBody801_412 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 54)

def sourceBody801_413 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 66, Flapjack.WordLangExpHOL.const 32#64])
  18

def sourceBody801_414 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_413 sourceBody801_2

def sourceBody801_415 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_412 sourceBody801_414

def sourceBody801_416 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 112)

def sourceBody801_417 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 66, Flapjack.WordLangExpHOL.const 40#64])
  18

def sourceBody801_418 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_417 sourceBody801_2

def sourceBody801_419 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_416 sourceBody801_418

def sourceBody801_420 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_419 sourceBody801_2

def sourceBody801_421 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_415 sourceBody801_420

def sourceBody801_422 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_411 sourceBody801_421

def sourceBody801_423 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_407 sourceBody801_422

def sourceBody801_424 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_403 sourceBody801_423

def sourceBody801_425 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_399 sourceBody801_424

def sourceBody801_426 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_395 sourceBody801_425

def sourceBody801_427 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_426

def sourceBody801_428 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_394 sourceBody801_427

def sourceBody801_429 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_428

def sourceBody801_430 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_393 sourceBody801_429

def sourceBody801_431 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_430

def sourceBody801_432 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_392 sourceBody801_431

def sourceBody801_433 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_432

def sourceBody801_434 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_391 sourceBody801_433

def sourceBody801_435 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_434

def sourceBody801_436 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_390 sourceBody801_435

def sourceBody801_437 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_436

def sourceBody801_438 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_389 sourceBody801_437

def sourceBody801_439 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_438

def sourceBody801_440 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_388 sourceBody801_439

def sourceBody801_441 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 66
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 48#64])

def sourceBody801_442 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.var 92)

def sourceBody801_443 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 96 (Flapjack.WordLangExpHOL.var 22)

def sourceBody801_444 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.var 78)

def sourceBody801_445 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 82 (Flapjack.WordLangExpHOL.var 50)

def sourceBody801_446 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.var 108)

def sourceBody801_447 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 112 (Flapjack.WordLangExpHOL.var 14)

def sourceBody801_448 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_447 sourceBody801_425

def sourceBody801_449 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_448

def sourceBody801_450 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_446 sourceBody801_449

def sourceBody801_451 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_450

def sourceBody801_452 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_445 sourceBody801_451

def sourceBody801_453 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_452

def sourceBody801_454 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_444 sourceBody801_453

def sourceBody801_455 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_454

def sourceBody801_456 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_443 sourceBody801_455

def sourceBody801_457 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_456

def sourceBody801_458 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_442 sourceBody801_457

def sourceBody801_459 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_458

def sourceBody801_460 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_441 sourceBody801_459

def sourceBody801_461 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_460

def sourceBody801_462 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_440 sourceBody801_461

def sourceBody801_463 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 66
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 96#64])

def sourceBody801_464 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 38 (Flapjack.WordLangExpHOL.const 8505329371266088957#64)

def sourceBody801_465 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 96 (Flapjack.WordLangExpHOL.const 17002214543764226050#64)

def sourceBody801_466 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 26 (Flapjack.WordLangExpHOL.const 6865905132761471162#64)

def sourceBody801_467 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 82 (Flapjack.WordLangExpHOL.const 8632934651105793861#64)

def sourceBody801_468 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 54 (Flapjack.WordLangExpHOL.const 6631298214892334189#64)

def sourceBody801_469 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 112 (Flapjack.WordLangExpHOL.const 1582556514881692819#64)

def sourceBody801_470 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_469 sourceBody801_425

def sourceBody801_471 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_470

def sourceBody801_472 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_468 sourceBody801_471

def sourceBody801_473 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_472

def sourceBody801_474 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_467 sourceBody801_473

def sourceBody801_475 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_474

def sourceBody801_476 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_466 sourceBody801_475

def sourceBody801_477 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_476

def sourceBody801_478 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_465 sourceBody801_477

def sourceBody801_479 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_478

def sourceBody801_480 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_464 sourceBody801_479

def sourceBody801_481 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_480

def sourceBody801_482 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_463 sourceBody801_481

def sourceBody801_483 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_482

def sourceBody801_484 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_462 sourceBody801_483

def sourceBody801_485 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [66]

def sourceBody801_486 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_485 sourceBody801_2

def sourceBody801_487 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_335 sourceBody801_486

def sourceBody801_488 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_484 sourceBody801_487

def sourceBody801_489 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_366 sourceBody801_488

def sourceBody801_490 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_489

def sourceBody801_491 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_490

def sourceBody801_492 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_350 sourceBody801_491

def sourceBody801_493 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_332 sourceBody801_492

def sourceBody801_494 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_493

def sourceBody801_495 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_494

def sourceBody801_496 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_304 sourceBody801_495

def sourceBody801_497 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_496

def sourceBody801_498 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_497

def sourceBody801_499 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_498

def sourceBody801_500 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_499

def sourceBody801_501 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_500

def sourceBody801_502 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_501

def sourceBody801_503 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_502

def sourceBody801_504 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_503

def sourceBody801_505 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_504

def sourceBody801_506 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_505

def sourceBody801_507 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_506

def sourceBody801_508 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_507

def sourceBody801_509 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_288 sourceBody801_508

def sourceBody801_510 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_509

def sourceBody801_511 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_510

def sourceBody801_512 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_511

def sourceBody801_513 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_512

def sourceBody801_514 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_513

def sourceBody801_515 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_514

def sourceBody801_516 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_515

def sourceBody801_517 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_516

def sourceBody801_518 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_517

def sourceBody801_519 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_518

def sourceBody801_520 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_519

def sourceBody801_521 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_520

def sourceBody801_522 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_268 sourceBody801_521

def sourceBody801_523 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_240 sourceBody801_522

def sourceBody801_524 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_523

def sourceBody801_525 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_239 sourceBody801_524

def sourceBody801_526 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_525

def sourceBody801_527 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_238 sourceBody801_526

def sourceBody801_528 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_527

def sourceBody801_529 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_237 sourceBody801_528

def sourceBody801_530 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_529

def sourceBody801_531 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_236 sourceBody801_530

def sourceBody801_532 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_531

def sourceBody801_533 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_235 sourceBody801_532

def sourceBody801_534 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_533

def sourceBody801_535 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_234 sourceBody801_534

def sourceBody801_536 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_207 sourceBody801_535

def sourceBody801_537 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_536

def sourceBody801_538 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_537

def sourceBody801_539 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_538

def sourceBody801_540 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_539

def sourceBody801_541 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_540

def sourceBody801_542 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_541

def sourceBody801_543 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_542

def sourceBody801_544 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_543

def sourceBody801_545 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_544

def sourceBody801_546 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_545

def sourceBody801_547 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_546

def sourceBody801_548 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_547

def sourceBody801_549 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_191 sourceBody801_548

def sourceBody801_550 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_549

def sourceBody801_551 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_550

def sourceBody801_552 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_551

def sourceBody801_553 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_552

def sourceBody801_554 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_553

def sourceBody801_555 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_554

def sourceBody801_556 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_555

def sourceBody801_557 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_556

def sourceBody801_558 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_557

def sourceBody801_559 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_558

def sourceBody801_560 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_559

def sourceBody801_561 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_560

def sourceBody801_562 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_175 sourceBody801_561

def sourceBody801_563 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_167 sourceBody801_562

def sourceBody801_564 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_563

def sourceBody801_565 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_564

def sourceBody801_566 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_146 sourceBody801_565

def sourceBody801_567 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_61 sourceBody801_566

def sourceBody801_568 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_567

def sourceBody801_569 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_568

def sourceBody801_570 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_569

def sourceBody801_571 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_570

def sourceBody801_572 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_571

def sourceBody801_573 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_572

def sourceBody801_574 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_573

def sourceBody801_575 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_574

def sourceBody801_576 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_575

def sourceBody801_577 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_576

def sourceBody801_578 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_577

def sourceBody801_579 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_578

def sourceBody801_580 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_55 sourceBody801_579

def sourceBody801_581 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_37 sourceBody801_580

def sourceBody801_582 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_581

def sourceBody801_583 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_582

def sourceBody801_584 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_31 sourceBody801_583

def sourceBody801_585 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_584

def sourceBody801_586 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_585

def sourceBody801_587 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_27 sourceBody801_586

def sourceBody801_588 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_8 sourceBody801_587

def sourceBody801_589 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_588

def sourceBody801_590 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_7 sourceBody801_589

def sourceBody801_591 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_590

def sourceBody801_592 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_6 sourceBody801_591

def sourceBody801_593 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_2 sourceBody801_592

def sourceBody801_594 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_5 sourceBody801_593

def sourceBody801_595 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody801_4 sourceBody801_594

def source801 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (801, 3, sourceBody801_595)
end InitECandidate.Proofs.WordStages
