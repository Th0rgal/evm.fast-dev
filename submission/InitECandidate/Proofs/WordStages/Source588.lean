import InitECandidate.Proofs.WordStages.Source572
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody588_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody588_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 4)

def sourceBody588_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody588_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody588_0, 588, 2)) (some 403) ([8]) (some (8, sourceBody588_2, 588, 3))

def sourceBody588_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody588_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody588_3 sourceBody588_4

def sourceBody588_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody588_5 sourceBody588_0

def sourceBody588_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody588_1 sourceBody588_6

def sourceBody588_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 48#64]))

def sourceBody588_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 4)

def sourceBody588_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody588_11 : WordLangProgHOL (BitVec 64) :=
.call (some (([8, 16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody588_0, 588, 4)) (some 404) ([12, 20]) (some (12, sourceBody588_10, 588, 5))

def sourceBody588_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody588_11 sourceBody588_4

def sourceBody588_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody588_12 sourceBody588_0

def sourceBody588_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody588_9 sourceBody588_13

def sourceBody588_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody588_8 sourceBody588_14

def sourceBody588_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 16)

def sourceBody588_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody588_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody588_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody588_20 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 20 (Flapjack.WordRegImm.reg 6) sourceBody588_18 sourceBody588_19

def sourceBody588_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody588_20 sourceBody588_4

def sourceBody588_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 20)

def sourceBody588_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 8)

def sourceBody588_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 16)

def sourceBody588_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody588_26 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody588_0, 588, 6)) (some 464) ([20, 6]) (some (20, sourceBody588_25, 588, 7))

def sourceBody588_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody588_26 sourceBody588_4

def sourceBody588_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody588_27 sourceBody588_0

def sourceBody588_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody588_24 sourceBody588_28

def sourceBody588_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody588_23 sourceBody588_29

def sourceBody588_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 12)

def sourceBody588_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody588_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody588_34 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 6 (Flapjack.WordRegImm.reg 14) sourceBody588_33 sourceBody588_17

def sourceBody588_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody588_34 sourceBody588_4

def sourceBody588_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 6)

def sourceBody588_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [20]

def sourceBody588_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody588_37 sourceBody588_0

def sourceBody588_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody588_19 sourceBody588_38

def sourceBody588_40 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.imm 0#64) sourceBody588_39 sourceBody588_0

def sourceBody588_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody588_40 sourceBody588_4

def sourceBody588_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody588_41 sourceBody588_0

def sourceBody588_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody588_36 sourceBody588_42

def sourceBody588_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody588_35 sourceBody588_43

def sourceBody588_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody588_32 sourceBody588_44

def sourceBody588_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody588_31 sourceBody588_45

def sourceBody588_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody588_30 sourceBody588_46

def sourceBody588_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody588_0 sourceBody588_47

def sourceBody588_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody588_0 sourceBody588_48

def sourceBody588_50 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.WordRegImm.imm 0#64) sourceBody588_49 sourceBody588_0

def sourceBody588_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody588_50 sourceBody588_4

def sourceBody588_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody588_51 sourceBody588_0

def sourceBody588_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody588_22 sourceBody588_52

def sourceBody588_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody588_21 sourceBody588_53

def sourceBody588_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody588_17 sourceBody588_54

def sourceBody588_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody588_16 sourceBody588_55

def sourceBody588_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 0#64]))

def sourceBody588_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 40#64]))

def sourceBody588_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody588_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [12]

def sourceBody588_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody588_60 sourceBody588_0

def sourceBody588_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody588_59 sourceBody588_61

def sourceBody588_63 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.WordRegImm.imm 0#64) sourceBody588_62 sourceBody588_0

def sourceBody588_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody588_63 sourceBody588_4

def sourceBody588_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody588_64 sourceBody588_0

def sourceBody588_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody588_22 sourceBody588_65

def sourceBody588_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody588_21 sourceBody588_66

def sourceBody588_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody588_58 sourceBody588_67

def sourceBody588_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody588_57 sourceBody588_68

def sourceBody588_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody588_56 sourceBody588_69

def sourceBody588_71 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody588_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody588_71 sourceBody588_61

def sourceBody588_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody588_70 sourceBody588_72

def sourceBody588_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody588_15 sourceBody588_73

def sourceBody588_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody588_0 sourceBody588_74

def sourceBody588_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody588_0 sourceBody588_75

def sourceBody588_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody588_0 sourceBody588_76

def sourceBody588_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody588_0 sourceBody588_77

def sourceBody588_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody588_7 sourceBody588_78

def sourceBody588_80 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody588_0 sourceBody588_79

def sourceBody588_81 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody588_0 sourceBody588_80

def source588 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (588, 3, sourceBody588_81)
end InitECandidate.Proofs.WordStages
