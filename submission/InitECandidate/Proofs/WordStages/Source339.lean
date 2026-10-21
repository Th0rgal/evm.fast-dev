import InitECandidate.Proofs.WordStages.Source323
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody339_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody339_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 2)

def sourceBody339_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 4)

def sourceBody339_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody339_4 : WordLangProgHOL (BitVec 64) :=
.call (some (([18, 8]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody339_0, 339, 2)) (some 169) ([16, 12]) (some (16, sourceBody339_3, 339, 3))

def sourceBody339_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody339_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody339_4 sourceBody339_5

def sourceBody339_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody339_6 sourceBody339_0

def sourceBody339_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody339_2 sourceBody339_7

def sourceBody339_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody339_1 sourceBody339_8

def sourceBody339_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 8)
    (Flapjack.WordLangExpHOL.const 5#64))

def sourceBody339_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody339_12 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody339_0, 339, 4)) (some 68) ([12]) (some (12, sourceBody339_11, 339, 5))

def sourceBody339_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody339_12 sourceBody339_5

def sourceBody339_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody339_13 sourceBody339_0

def sourceBody339_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody339_10 sourceBody339_14

def sourceBody339_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody339_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 12)

def sourceBody339_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 8)

def sourceBody339_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody339_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody339_21 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 6 (Flapjack.WordRegImm.reg 14) sourceBody339_19 sourceBody339_20

def sourceBody339_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody339_21 sourceBody339_5

def sourceBody339_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 6)

def sourceBody339_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 18)

def sourceBody339_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 12)

def sourceBody339_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody339_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody339_28 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody339_0, 339, 6)) (some 335) ([6, 14, 10]) (some (6, sourceBody339_27, 339, 7))

def sourceBody339_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody339_28 sourceBody339_5

def sourceBody339_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody339_29 sourceBody339_0

def sourceBody339_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody339_26 sourceBody339_30

def sourceBody339_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody339_25 sourceBody339_31

def sourceBody339_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody339_24 sourceBody339_32

def sourceBody339_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
    [Flapjack.WordLangExpHOL.var 16,
      Flapjack.WordLangExpHOL.shift Flapjack.Shift.lsl (Flapjack.WordLangExpHOL.var 12)
        (Flapjack.WordLangExpHOL.const 5#64)])

def sourceBody339_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 22)

def sourceBody339_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody339_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody339_38 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody339_0, 339, 8)) (some 77) ([14, 10, 20]) (some (14, sourceBody339_37, 339, 9))

def sourceBody339_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody339_38 sourceBody339_5

def sourceBody339_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody339_39 sourceBody339_0

def sourceBody339_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody339_36 sourceBody339_40

def sourceBody339_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody339_35 sourceBody339_41

def sourceBody339_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody339_34 sourceBody339_42

def sourceBody339_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody339_0 sourceBody339_43

def sourceBody339_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody339_0 sourceBody339_44

def sourceBody339_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody339_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 6)

def sourceBody339_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody339_47 sourceBody339_0

def sourceBody339_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody339_48 sourceBody339_0

def sourceBody339_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody339_46 sourceBody339_49

def sourceBody339_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody339_0 sourceBody339_50

def sourceBody339_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody339_45 sourceBody339_51

def sourceBody339_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody339_33 sourceBody339_52

def sourceBody339_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody339_0 sourceBody339_53

def sourceBody339_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody339_0 sourceBody339_54

def sourceBody339_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.continue 0

def sourceBody339_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody339_55 sourceBody339_56

def sourceBody339_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.break 0

def sourceBody339_59 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.imm 0#64) sourceBody339_57 sourceBody339_58

def sourceBody339_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody339_59 sourceBody339_5

def sourceBody339_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody339_60 sourceBody339_0

def sourceBody339_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody339_23 sourceBody339_61

def sourceBody339_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody339_22 sourceBody339_62

def sourceBody339_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody339_18 sourceBody339_63

def sourceBody339_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody339_17 sourceBody339_64

def sourceBody339_66 : WordLangProgHOL (BitVec 64) :=
.loop (Flapjack.Spt.bs
  (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
  PUnit.unit Flapjack.Spt.ln) sourceBody339_65 (Flapjack.Spt.bs
  (Flapjack.Spt.bn Flapjack.Spt.ln
    (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
  PUnit.unit Flapjack.Spt.ln)

def sourceBody339_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody339_66 sourceBody339_5

def sourceBody339_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody339_5 sourceBody339_67

def sourceBody339_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 16)

def sourceBody339_70 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 8)

def sourceBody339_71 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [22, 6]

def sourceBody339_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody339_71 sourceBody339_0

def sourceBody339_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody339_70 sourceBody339_72

def sourceBody339_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody339_69 sourceBody339_73

def sourceBody339_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody339_68 sourceBody339_74

def sourceBody339_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody339_16 sourceBody339_75

def sourceBody339_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody339_0 sourceBody339_76

def sourceBody339_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody339_15 sourceBody339_77

def sourceBody339_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody339_0 sourceBody339_78

def sourceBody339_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody339_0 sourceBody339_79

def sourceBody339_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody339_9 sourceBody339_80

def sourceBody339_82 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody339_0 sourceBody339_81

def sourceBody339_83 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody339_0 sourceBody339_82

def sourceBody339_84 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody339_0 sourceBody339_83

def sourceBody339_85 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody339_0 sourceBody339_84

def source339 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (339, 3, sourceBody339_85)
end InitECandidate.Proofs.WordStages
