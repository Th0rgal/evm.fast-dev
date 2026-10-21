import InitECandidate.Proofs.WordStages.Source664
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody680_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 2)
    (Flapjack.WordLangExpHOL.const 5#64))

def sourceBody680_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 34 (Flapjack.WordLangExpHOL.const 3#64)

def sourceBody680_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.longMul 26 26 18 34))

def sourceBody680_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody680_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_2 sourceBody680_3

def sourceBody680_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_1 sourceBody680_4

def sourceBody680_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_0 sourceBody680_5

def sourceBody680_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 42 (Flapjack.WordLangExpHOL.var 26)

def sourceBody680_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 38

def sourceBody680_9 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln))
      PUnit.unit (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody680_3, 680, 2)) (some 69) ([]) (some (38, sourceBody680_8, 680, 3))

def sourceBody680_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody680_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_9 sourceBody680_10

def sourceBody680_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_11 sourceBody680_3

def sourceBody680_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 30 (Flapjack.WordLangExpHOL.var 42)

def sourceBody680_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 30

def sourceBody680_15 : WordLangProgHOL (BitVec 64) :=
.call (some (([38]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln))
      PUnit.unit (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody680_3, 680, 4)) (some 68) ([30]) (some (30, sourceBody680_14, 680, 5))

def sourceBody680_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_15 sourceBody680_10

def sourceBody680_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_16 sourceBody680_3

def sourceBody680_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_13 sourceBody680_17

def sourceBody680_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 44 (Flapjack.WordLangExpHOL.var 42)

def sourceBody680_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 44

def sourceBody680_21 : WordLangProgHOL (BitVec 64) :=
.call (some (([30]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln))
      PUnit.unit (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody680_3, 680, 6)) (some 68) ([44]) (some (44, sourceBody680_20, 680, 7))

def sourceBody680_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_21 sourceBody680_10

def sourceBody680_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_22 sourceBody680_3

def sourceBody680_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_19 sourceBody680_23

def sourceBody680_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 2)

def sourceBody680_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 38)

def sourceBody680_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody680_28 : WordLangProgHOL (BitVec 64) :=
.call (some (([44]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln))
      PUnit.unit (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody680_3, 680, 8)) (some 676) ([16, 32]) (some (16, sourceBody680_27, 680, 9))

def sourceBody680_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_28 sourceBody680_10

def sourceBody680_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_29 sourceBody680_3

def sourceBody680_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_26 sourceBody680_30

def sourceBody680_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_25 sourceBody680_31

def sourceBody680_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_3 sourceBody680_32

def sourceBody680_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_3 sourceBody680_33

def sourceBody680_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 30)

def sourceBody680_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 6)

def sourceBody680_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 42)

def sourceBody680_38 : WordLangProgHOL (BitVec 64) :=
.call (some (([44]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln))
      PUnit.unit (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody680_3, 680, 10)) (some 77) ([16, 32, 24]) (some (16, sourceBody680_27, 680, 11))

def sourceBody680_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_38 sourceBody680_10

def sourceBody680_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_39 sourceBody680_3

def sourceBody680_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_37 sourceBody680_40

def sourceBody680_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_36 sourceBody680_41

def sourceBody680_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_35 sourceBody680_42

def sourceBody680_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_3 sourceBody680_43

def sourceBody680_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_3 sourceBody680_44

def sourceBody680_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_34 sourceBody680_45

def sourceBody680_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 8)

def sourceBody680_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.var 10)

def sourceBody680_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 12)

def sourceBody680_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 14)

def sourceBody680_51 : WordLangProgHOL (BitVec 64) :=
.call (some (([44]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln))
      PUnit.unit (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody680_3, 680, 12)) (some 138) ([16, 32, 24, 40]) (some (16, sourceBody680_27, 680, 13))

def sourceBody680_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_51 sourceBody680_10

def sourceBody680_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_52 sourceBody680_3

def sourceBody680_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_50 sourceBody680_53

def sourceBody680_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_49 sourceBody680_54

def sourceBody680_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_48 sourceBody680_55

def sourceBody680_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_47 sourceBody680_56

def sourceBody680_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody680_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 16)

def sourceBody680_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 44)

def sourceBody680_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody680_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody680_63 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 24 (Flapjack.WordRegImm.reg 40) sourceBody680_61 sourceBody680_62

def sourceBody680_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_63 sourceBody680_10

def sourceBody680_65 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 24)

def sourceBody680_66 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 8)

def sourceBody680_67 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 10)

def sourceBody680_68 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 12)

def sourceBody680_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 14)

def sourceBody680_70 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 16)

def sourceBody680_71 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 24

def sourceBody680_72 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)
        PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody680_3, 680, 14)) (some 104) ([24, 40, 20, 36, 28]) (some (24, sourceBody680_71, 680, 15))

def sourceBody680_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_72 sourceBody680_10

def sourceBody680_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_73 sourceBody680_3

def sourceBody680_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_70 sourceBody680_74

def sourceBody680_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_69 sourceBody680_75

def sourceBody680_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_68 sourceBody680_76

def sourceBody680_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_67 sourceBody680_77

def sourceBody680_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_66 sourceBody680_78

def sourceBody680_80 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 32)

def sourceBody680_81 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody680_82 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody680_83 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody680_84 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 40 (Flapjack.WordRegImm.reg 20) sourceBody680_82 sourceBody680_83

def sourceBody680_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_84 sourceBody680_10

def sourceBody680_86 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 40)

def sourceBody680_87 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 2)

def sourceBody680_88 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 38)

def sourceBody680_89 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 38)

def sourceBody680_90 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 28 (Flapjack.WordLangExpHOL.var 30)

def sourceBody680_91 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 40

def sourceBody680_92 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)
        PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody680_3, 680, 16)) (some 679) ([40, 20, 36, 28]) (some (40, sourceBody680_91, 680, 17))

def sourceBody680_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_92 sourceBody680_10

def sourceBody680_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_93 sourceBody680_3

def sourceBody680_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_90 sourceBody680_94

def sourceBody680_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_89 sourceBody680_95

def sourceBody680_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_88 sourceBody680_96

def sourceBody680_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_87 sourceBody680_97

def sourceBody680_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_3 sourceBody680_98

def sourceBody680_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_3 sourceBody680_99

def sourceBody680_101 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 36 (Flapjack.WordRegImm.imm 0#64) sourceBody680_100 sourceBody680_3

def sourceBody680_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_101 sourceBody680_10

def sourceBody680_103 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_102 sourceBody680_3

def sourceBody680_104 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_86 sourceBody680_103

def sourceBody680_105 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_85 sourceBody680_104

def sourceBody680_106 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_81 sourceBody680_105

def sourceBody680_107 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_80 sourceBody680_106

def sourceBody680_108 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 16, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody680_109 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 24)

def sourceBody680_110 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_109 sourceBody680_3

def sourceBody680_111 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_110 sourceBody680_3

def sourceBody680_112 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_108 sourceBody680_111

def sourceBody680_113 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_3 sourceBody680_112

def sourceBody680_114 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_107 sourceBody680_113

def sourceBody680_115 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 16)

def sourceBody680_116 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 44)

def sourceBody680_117 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 40 (Flapjack.WordRegImm.reg 20) sourceBody680_82 sourceBody680_83

def sourceBody680_118 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_117 sourceBody680_10

def sourceBody680_119 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 30)

def sourceBody680_120 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 36 (Flapjack.WordLangExpHOL.var 30)

def sourceBody680_121 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
          (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
        PUnit.unit
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln))
      PUnit.unit
      (Flapjack.Spt.bs
        (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)
        PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody680_3, 680, 18)) (some 678) ([40, 20, 36]) (some (40, sourceBody680_91, 680, 19))

def sourceBody680_122 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_121 sourceBody680_10

def sourceBody680_123 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_122 sourceBody680_3

def sourceBody680_124 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_120 sourceBody680_123

def sourceBody680_125 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_119 sourceBody680_124

def sourceBody680_126 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_87 sourceBody680_125

def sourceBody680_127 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_3 sourceBody680_126

def sourceBody680_128 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_3 sourceBody680_127

def sourceBody680_129 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 36 (Flapjack.WordRegImm.imm 0#64) sourceBody680_128 sourceBody680_3

def sourceBody680_130 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_129 sourceBody680_10

def sourceBody680_131 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_130 sourceBody680_3

def sourceBody680_132 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_86 sourceBody680_131

def sourceBody680_133 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_118 sourceBody680_132

def sourceBody680_134 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_116 sourceBody680_133

def sourceBody680_135 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_115 sourceBody680_134

def sourceBody680_136 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_114 sourceBody680_135

def sourceBody680_137 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_79 sourceBody680_136

def sourceBody680_138 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_3 sourceBody680_137

def sourceBody680_139 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_3 sourceBody680_138

def sourceBody680_140 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody680_141 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_139 sourceBody680_140

def sourceBody680_142 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody680_143 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 20 (Flapjack.WordRegImm.imm 0#64) sourceBody680_141 sourceBody680_142

def sourceBody680_144 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_143 sourceBody680_10

def sourceBody680_145 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_144 sourceBody680_3

def sourceBody680_146 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_65 sourceBody680_145

def sourceBody680_147 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_64 sourceBody680_146

def sourceBody680_148 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_60 sourceBody680_147

def sourceBody680_149 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_59 sourceBody680_148

def sourceBody680_150 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln))
    PUnit.unit
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)
      PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
  PUnit.unit Flapjack.Spt.ln) sourceBody680_149 (Flapjack.Spt.bs
  (Flapjack.Spt.bn
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln))
    (Flapjack.Spt.ls PUnit.unit))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody680_151 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_150 sourceBody680_10

def sourceBody680_152 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_10 sourceBody680_151

def sourceBody680_153 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 4)

def sourceBody680_154 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 40 (Flapjack.WordLangExpHOL.var 38)

def sourceBody680_155 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 42)

def sourceBody680_156 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody680_3, 680, 20)) (some 77) ([24, 40, 20]) (some (24, sourceBody680_71, 680, 21))

def sourceBody680_157 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_156 sourceBody680_10

def sourceBody680_158 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_157 sourceBody680_3

def sourceBody680_159 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_155 sourceBody680_158

def sourceBody680_160 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_154 sourceBody680_159

def sourceBody680_161 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_153 sourceBody680_160

def sourceBody680_162 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_3 sourceBody680_161

def sourceBody680_163 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_3 sourceBody680_162

def sourceBody680_164 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_152 sourceBody680_163

def sourceBody680_165 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 22)

def sourceBody680_166 : WordLangProgHOL (BitVec 64) :=
.call (some (([32]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody680_3, 680, 22)) (some 70) ([24]) (some (24, sourceBody680_71, 680, 23))

def sourceBody680_167 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_166 sourceBody680_10

def sourceBody680_168 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_167 sourceBody680_3

def sourceBody680_169 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_165 sourceBody680_168

def sourceBody680_170 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_3 sourceBody680_169

def sourceBody680_171 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_3 sourceBody680_170

def sourceBody680_172 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_164 sourceBody680_171

def sourceBody680_173 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 32 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody680_174 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [32]

def sourceBody680_175 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_174 sourceBody680_3

def sourceBody680_176 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_173 sourceBody680_175

def sourceBody680_177 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_172 sourceBody680_176

def sourceBody680_178 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_58 sourceBody680_177

def sourceBody680_179 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_3 sourceBody680_178

def sourceBody680_180 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_57 sourceBody680_179

def sourceBody680_181 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_3 sourceBody680_180

def sourceBody680_182 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_3 sourceBody680_181

def sourceBody680_183 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_46 sourceBody680_182

def sourceBody680_184 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_24 sourceBody680_183

def sourceBody680_185 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_3 sourceBody680_184

def sourceBody680_186 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_3 sourceBody680_185

def sourceBody680_187 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_18 sourceBody680_186

def sourceBody680_188 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_3 sourceBody680_187

def sourceBody680_189 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_3 sourceBody680_188

def sourceBody680_190 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_12 sourceBody680_189

def sourceBody680_191 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_3 sourceBody680_190

def sourceBody680_192 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_3 sourceBody680_191

def sourceBody680_193 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_7 sourceBody680_192

def sourceBody680_194 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody680_6 sourceBody680_193

def source680 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (680, 8, sourceBody680_194)
end InitECandidate.Proofs.WordStages
