import InitECandidate.Proofs.WordStages.Source827
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody843_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody843_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody843_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody843_0, 843, 2)) (some 69) ([]) (some (18, sourceBody843_1, 843, 3))

def sourceBody843_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody843_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody843_2 sourceBody843_3

def sourceBody843_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody843_4 sourceBody843_0

def sourceBody843_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 4)
        (Flapjack.WordLangExpHOL.const 5#64),
      Flapjack.WordLangExpHOL.const 8#64])

def sourceBody843_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody843_8 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody843_0, 843, 4)) (some 68) ([14]) (some (14, sourceBody843_7, 843, 5))

def sourceBody843_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody843_8 sourceBody843_3

def sourceBody843_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody843_9 sourceBody843_0

def sourceBody843_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody843_6 sourceBody843_10

def sourceBody843_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody843_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 14)

def sourceBody843_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 4)

def sourceBody843_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody843_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody843_17 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.less) 8 (Flapjack.WordRegImm.reg 16) sourceBody843_15 sourceBody843_16

def sourceBody843_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody843_17 sourceBody843_3

def sourceBody843_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 8)

def sourceBody843_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 14)
          (Flapjack.WordLangExpHOL.const 4#64)]))

def sourceBody843_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2,
        Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 14)
          (Flapjack.WordLangExpHOL.const 4#64),
        Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody843_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 18,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 14)
        (Flapjack.WordLangExpHOL.const 5#64)])

def sourceBody843_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody843_24 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody843_0, 843, 6)) (some 153) ([8, 16, 12]) (some (8, sourceBody843_23, 843, 7))

def sourceBody843_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody843_24 sourceBody843_3

def sourceBody843_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody843_25 sourceBody843_0

def sourceBody843_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody843_22 sourceBody843_26

def sourceBody843_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody843_21 sourceBody843_27

def sourceBody843_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody843_20 sourceBody843_28

def sourceBody843_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody843_0 sourceBody843_29

def sourceBody843_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody843_0 sourceBody843_30

def sourceBody843_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody843_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 20)

def sourceBody843_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody843_33 sourceBody843_0

def sourceBody843_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody843_34 sourceBody843_0

def sourceBody843_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody843_32 sourceBody843_35

def sourceBody843_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody843_0 sourceBody843_36

def sourceBody843_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody843_31 sourceBody843_37

def sourceBody843_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody843_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody843_38 sourceBody843_39

def sourceBody843_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody843_42 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 12 (Flapjack.WordRegImm.imm 0#64) sourceBody843_40 sourceBody843_41

def sourceBody843_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody843_42 sourceBody843_3

def sourceBody843_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody843_43 sourceBody843_0

def sourceBody843_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody843_19 sourceBody843_44

def sourceBody843_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody843_18 sourceBody843_45

def sourceBody843_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody843_14 sourceBody843_46

def sourceBody843_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody843_13 sourceBody843_47

def sourceBody843_49 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit (Flapjack.Spt.ls PUnit.unit))
  PUnit.unit Flapjack.Spt.ln) sourceBody843_48 (Flapjack.Spt.bs
  (Flapjack.Spt.bn
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    (Flapjack.Spt.ls PUnit.unit))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody843_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody843_49 sourceBody843_3

def sourceBody843_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody843_3 sourceBody843_50

def sourceBody843_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 18)

def sourceBody843_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 4)
    (Flapjack.WordLangExpHOL.const 5#64))

def sourceBody843_54 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 6)

def sourceBody843_55 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody843_0, 843, 8)) (some 153) ([8, 16, 12]) (some (8, sourceBody843_23, 843, 9))

def sourceBody843_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody843_55 sourceBody843_3

def sourceBody843_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody843_56 sourceBody843_0

def sourceBody843_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody843_54 sourceBody843_57

def sourceBody843_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody843_53 sourceBody843_58

def sourceBody843_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody843_52 sourceBody843_59

def sourceBody843_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody843_0 sourceBody843_60

def sourceBody843_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody843_0 sourceBody843_61

def sourceBody843_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody843_51 sourceBody843_62

def sourceBody843_64 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 10)

def sourceBody843_65 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody843_0, 843, 10)) (some 70) ([8]) (some (8, sourceBody843_23, 843, 11))

def sourceBody843_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody843_65 sourceBody843_3

def sourceBody843_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody843_66 sourceBody843_0

def sourceBody843_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody843_64 sourceBody843_67

def sourceBody843_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody843_0 sourceBody843_68

def sourceBody843_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody843_0 sourceBody843_69

def sourceBody843_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody843_63 sourceBody843_70

def sourceBody843_72 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody843_73 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [20]

def sourceBody843_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody843_73 sourceBody843_0

def sourceBody843_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody843_72 sourceBody843_74

def sourceBody843_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody843_71 sourceBody843_75

def sourceBody843_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody843_12 sourceBody843_76

def sourceBody843_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody843_0 sourceBody843_77

def sourceBody843_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody843_11 sourceBody843_78

def sourceBody843_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody843_0 sourceBody843_79

def sourceBody843_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody843_0 sourceBody843_80

def sourceBody843_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody843_5 sourceBody843_81

def sourceBody843_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody843_0 sourceBody843_82

def sourceBody843_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody843_0 sourceBody843_83

def source843 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (843, 4, sourceBody843_84)
end InitECandidate.Proofs.WordStages
