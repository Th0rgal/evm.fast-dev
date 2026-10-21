import InitECandidate.Proofs.WordStages.Source417
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody433_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody433_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody433_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody433_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 20)

def sourceBody433_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 8)

def sourceBody433_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody433_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody433_7 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notLower) 14 (Flapjack.WordRegImm.reg 24) sourceBody433_5 sourceBody433_6

def sourceBody433_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody433_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody433_7 sourceBody433_8

def sourceBody433_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 14)

def sourceBody433_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 4)

def sourceBody433_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.longMul 6 6 14 24))

def sourceBody433_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 6)
    (Flapjack.WordLangExpHOL.const 1#64))

def sourceBody433_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody433_15 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody433_0, 433, 2)) (some 68) ([16]) (some (14, sourceBody433_14, 433, 3))

def sourceBody433_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody433_15 sourceBody433_8

def sourceBody433_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody433_16 sourceBody433_0

def sourceBody433_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody433_13 sourceBody433_17

def sourceBody433_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody433_12 sourceBody433_18

def sourceBody433_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody433_4 sourceBody433_19

def sourceBody433_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody433_11 sourceBody433_20

def sourceBody433_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 4)

def sourceBody433_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 20)

def sourceBody433_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.longMul 16 16 24 6))

def sourceBody433_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 18)

def sourceBody433_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 0#64]))

def sourceBody433_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 16)

def sourceBody433_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 24

def sourceBody433_29 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
        (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody433_0, 433, 4)) (some 77) ([12, 22, 10]) (some (24, sourceBody433_28, 433, 5))

def sourceBody433_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody433_29 sourceBody433_8

def sourceBody433_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody433_30 sourceBody433_0

def sourceBody433_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody433_27 sourceBody433_31

def sourceBody433_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody433_26 sourceBody433_32

def sourceBody433_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody433_25 sourceBody433_33

def sourceBody433_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody433_24 sourceBody433_34

def sourceBody433_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody433_23 sourceBody433_35

def sourceBody433_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody433_22 sourceBody433_36

def sourceBody433_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody433_0 sourceBody433_37

def sourceBody433_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody433_0 sourceBody433_38

def sourceBody433_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 0#64])

def sourceBody433_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 18)

def sourceBody433_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 24)

def sourceBody433_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 14) 6

def sourceBody433_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody433_43 sourceBody433_0

def sourceBody433_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody433_42 sourceBody433_44

def sourceBody433_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody433_45 sourceBody433_0

def sourceBody433_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody433_41 sourceBody433_46

def sourceBody433_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody433_0 sourceBody433_47

def sourceBody433_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody433_40 sourceBody433_48

def sourceBody433_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody433_0 sourceBody433_49

def sourceBody433_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody433_39 sourceBody433_50

def sourceBody433_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 16#64])

def sourceBody433_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 8)
    (Flapjack.WordLangExpHOL.const 1#64))

def sourceBody433_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody433_53 sourceBody433_46

def sourceBody433_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody433_0 sourceBody433_54

def sourceBody433_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody433_52 sourceBody433_55

def sourceBody433_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody433_0 sourceBody433_56

def sourceBody433_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody433_51 sourceBody433_57

def sourceBody433_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody433_21 sourceBody433_58

def sourceBody433_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody433_0 sourceBody433_59

def sourceBody433_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody433_0 sourceBody433_60

def sourceBody433_62 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.WordRegImm.imm 0#64) sourceBody433_61 sourceBody433_0

def sourceBody433_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody433_62 sourceBody433_8

def sourceBody433_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody433_63 sourceBody433_0

def sourceBody433_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody433_10 sourceBody433_64

def sourceBody433_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody433_9 sourceBody433_65

def sourceBody433_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody433_4 sourceBody433_66

def sourceBody433_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody433_3 sourceBody433_67

def sourceBody433_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 8#64])

def sourceBody433_70 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 20, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody433_71 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 14)

def sourceBody433_72 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 18) 24

def sourceBody433_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody433_72 sourceBody433_0

def sourceBody433_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody433_71 sourceBody433_73

def sourceBody433_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody433_74 sourceBody433_0

def sourceBody433_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody433_70 sourceBody433_75

def sourceBody433_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody433_0 sourceBody433_76

def sourceBody433_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody433_69 sourceBody433_77

def sourceBody433_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody433_0 sourceBody433_78

def sourceBody433_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody433_68 sourceBody433_79

def sourceBody433_81 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 20)

def sourceBody433_82 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst (Flapjack.WordLangInst.arith (Flapjack.WordLangArith.longMul 24 24 18 14))

def sourceBody433_83 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.load
        (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
          [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 0#64]),
      Flapjack.WordLangExpHOL.var 24])

def sourceBody433_84 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [6]

def sourceBody433_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody433_84 sourceBody433_0

def sourceBody433_86 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody433_83 sourceBody433_85

def sourceBody433_87 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody433_82 sourceBody433_86

def sourceBody433_88 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody433_11 sourceBody433_87

def sourceBody433_89 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody433_81 sourceBody433_88

def sourceBody433_90 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody433_80 sourceBody433_89

def sourceBody433_91 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody433_2 sourceBody433_90

def sourceBody433_92 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody433_0 sourceBody433_91

def sourceBody433_93 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody433_1 sourceBody433_92

def sourceBody433_94 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody433_0 sourceBody433_93

def source433 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (433, 3, sourceBody433_94)
end InitECandidate.Proofs.WordStages
