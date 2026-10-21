import InitECandidate.Proofs.WordStages.Source672
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody688_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody688_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 12#64)

def sourceBody688_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 2)

def sourceBody688_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody688_4 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody688_0, 688, 2)) (some 675) ([14, 22]) (some (14, sourceBody688_3, 688, 3))

def sourceBody688_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody688_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody688_4 sourceBody688_5

def sourceBody688_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody688_6 sourceBody688_0

def sourceBody688_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody688_2 sourceBody688_7

def sourceBody688_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody688_1 sourceBody688_8

def sourceBody688_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody688_0 sourceBody688_9

def sourceBody688_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody688_0 sourceBody688_10

def sourceBody688_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody688_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 8)
    (Flapjack.WordLangExpHOL.const 6#64))

def sourceBody688_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody688_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 14)

def sourceBody688_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody688_17 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 10 (Flapjack.WordRegImm.reg 16) sourceBody688_16 sourceBody688_14

def sourceBody688_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody688_17 sourceBody688_5

def sourceBody688_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 10)

def sourceBody688_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody688_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 22)

def sourceBody688_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody688_21 sourceBody688_0

def sourceBody688_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody688_22 sourceBody688_0

def sourceBody688_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody688_20 sourceBody688_23

def sourceBody688_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody688_0 sourceBody688_24

def sourceBody688_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 18)

def sourceBody688_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody688_28 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 10 (Flapjack.WordRegImm.reg 16) sourceBody688_16 sourceBody688_14

def sourceBody688_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody688_28 sourceBody688_5

def sourceBody688_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 2)

def sourceBody688_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 2)

def sourceBody688_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody688_33 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody688_0, 688, 4)) (some 665) ([10, 16]) (some (10, sourceBody688_32, 688, 5))

def sourceBody688_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody688_33 sourceBody688_5

def sourceBody688_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody688_34 sourceBody688_0

def sourceBody688_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody688_31 sourceBody688_35

def sourceBody688_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody688_30 sourceBody688_36

def sourceBody688_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody688_0 sourceBody688_37

def sourceBody688_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody688_0 sourceBody688_38

def sourceBody688_40 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.imm 0#64) sourceBody688_39 sourceBody688_0

def sourceBody688_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody688_40 sourceBody688_5

def sourceBody688_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody688_41 sourceBody688_0

def sourceBody688_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody688_19 sourceBody688_42

def sourceBody688_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody688_29 sourceBody688_43

def sourceBody688_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody688_27 sourceBody688_44

def sourceBody688_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody688_26 sourceBody688_45

def sourceBody688_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody688_25 sourceBody688_46

def sourceBody688_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and
    [Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr
        (Flapjack.WordLangExpHOL.load
          (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
            [Flapjack.WordLangExpHOL.var 6,
              Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl
                (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsr (Flapjack.WordLangExpHOL.var 14)
                  (Flapjack.WordLangExpHOL.const 6#64))
                (Flapjack.WordLangExpHOL.const 3#64)]))
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and
          [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 63#64]),
      Flapjack.WordLangExpHOL.const 1#64])

def sourceBody688_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 22)

def sourceBody688_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody688_51 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody688_52 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 16 (Flapjack.WordRegImm.reg 12) sourceBody688_27 sourceBody688_51

def sourceBody688_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody688_52 sourceBody688_5

def sourceBody688_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 16)

def sourceBody688_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 2)

def sourceBody688_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 4)

def sourceBody688_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody688_58 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody688_0, 688, 6)) (some 664) ([16, 12, 20]) (some (16, sourceBody688_57, 688, 7))

def sourceBody688_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody688_58 sourceBody688_5

def sourceBody688_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody688_59 sourceBody688_0

def sourceBody688_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody688_56 sourceBody688_60

def sourceBody688_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody688_55 sourceBody688_61

def sourceBody688_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody688_31 sourceBody688_62

def sourceBody688_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody688_0 sourceBody688_63

def sourceBody688_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody688_0 sourceBody688_64

def sourceBody688_66 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody688_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody688_66 sourceBody688_0

def sourceBody688_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody688_67 sourceBody688_0

def sourceBody688_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody688_65 sourceBody688_68

def sourceBody688_70 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 20 (Flapjack.WordRegImm.imm 0#64) sourceBody688_69 sourceBody688_0

def sourceBody688_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody688_70 sourceBody688_5

def sourceBody688_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody688_71 sourceBody688_0

def sourceBody688_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody688_54 sourceBody688_72

def sourceBody688_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody688_53 sourceBody688_73

def sourceBody688_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody688_50 sourceBody688_74

def sourceBody688_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody688_49 sourceBody688_75

def sourceBody688_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody688_48 sourceBody688_76

def sourceBody688_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody688_0 sourceBody688_77

def sourceBody688_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody688_47 sourceBody688_78

def sourceBody688_80 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody688_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody688_79 sourceBody688_80

def sourceBody688_82 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody688_83 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.imm 0#64) sourceBody688_81 sourceBody688_82

def sourceBody688_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody688_83 sourceBody688_5

def sourceBody688_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody688_84 sourceBody688_0

def sourceBody688_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody688_19 sourceBody688_85

def sourceBody688_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody688_18 sourceBody688_86

def sourceBody688_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody688_15 sourceBody688_87

def sourceBody688_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody688_14 sourceBody688_88

def sourceBody688_90 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
  PUnit.unit Flapjack.Spt.ln) sourceBody688_89 (Flapjack.Spt.ls PUnit.unit)

def sourceBody688_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody688_90 sourceBody688_5

def sourceBody688_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody688_5 sourceBody688_91

def sourceBody688_93 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody688_94 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [22]

def sourceBody688_95 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody688_94 sourceBody688_0

def sourceBody688_96 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody688_93 sourceBody688_95

def sourceBody688_97 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody688_92 sourceBody688_96

def sourceBody688_98 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody688_13 sourceBody688_97

def sourceBody688_99 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody688_0 sourceBody688_98

def sourceBody688_100 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody688_12 sourceBody688_99

def sourceBody688_101 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody688_0 sourceBody688_100

def sourceBody688_102 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody688_11 sourceBody688_101

def source688 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (688, 5, sourceBody688_102)
end InitECandidate.Proofs.WordStages
