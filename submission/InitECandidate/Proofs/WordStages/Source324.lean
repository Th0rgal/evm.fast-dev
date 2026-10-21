import InitECandidate.Proofs.WordStages.Source308
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody324_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody324_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody324_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 6)

def sourceBody324_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody324_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody324_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody324_6 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 4 (Flapjack.WordRegImm.reg 10) sourceBody324_4 sourceBody324_5

def sourceBody324_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody324_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody324_6 sourceBody324_7

def sourceBody324_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 4)

def sourceBody324_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 6)

def sourceBody324_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [12]

def sourceBody324_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody324_11 sourceBody324_0

def sourceBody324_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody324_10 sourceBody324_12

def sourceBody324_14 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.WordRegImm.imm 0#64) sourceBody324_13 sourceBody324_0

def sourceBody324_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody324_14 sourceBody324_7

def sourceBody324_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody324_15 sourceBody324_0

def sourceBody324_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody324_9 sourceBody324_16

def sourceBody324_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody324_8 sourceBody324_17

def sourceBody324_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody324_3 sourceBody324_18

def sourceBody324_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody324_2 sourceBody324_19

def sourceBody324_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody324_22 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 4 (Flapjack.WordRegImm.reg 10) sourceBody324_4 sourceBody324_5

def sourceBody324_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody324_22 sourceBody324_7

def sourceBody324_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 13#64)

def sourceBody324_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 4

def sourceBody324_26 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln, Flapjack.Spt.ln)), sourceBody324_0, 324, 2)) (some 282) ([4]) (some (4, sourceBody324_25, 324, 3))

def sourceBody324_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody324_26 sourceBody324_7

def sourceBody324_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody324_27 sourceBody324_0

def sourceBody324_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody324_24 sourceBody324_28

def sourceBody324_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody324_0 sourceBody324_29

def sourceBody324_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody324_0 sourceBody324_30

def sourceBody324_32 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 8 (Flapjack.WordRegImm.imm 0#64) sourceBody324_31 sourceBody324_0

def sourceBody324_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody324_32 sourceBody324_7

def sourceBody324_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody324_33 sourceBody324_0

def sourceBody324_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody324_9 sourceBody324_34

def sourceBody324_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody324_23 sourceBody324_35

def sourceBody324_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody324_3 sourceBody324_36

def sourceBody324_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody324_21 sourceBody324_37

def sourceBody324_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody324_20 sourceBody324_38

def sourceBody324_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody324_41 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln, Flapjack.Spt.ln)), sourceBody324_0, 324, 4)) (some 68) ([4]) (some (4, sourceBody324_25, 324, 5))

def sourceBody324_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody324_41 sourceBody324_7

def sourceBody324_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody324_42 sourceBody324_0

def sourceBody324_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody324_40 sourceBody324_43

def sourceBody324_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 8#64]))

def sourceBody324_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 16#64]))

def sourceBody324_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 12)

def sourceBody324_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody324_49 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody324_0, 324, 6)) (some 158) ([10, 8, 14]) (some (10, sourceBody324_48, 324, 7))

def sourceBody324_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody324_49 sourceBody324_7

def sourceBody324_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody324_50 sourceBody324_0

def sourceBody324_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody324_47 sourceBody324_51

def sourceBody324_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody324_46 sourceBody324_52

def sourceBody324_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody324_45 sourceBody324_53

def sourceBody324_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody324_0 sourceBody324_54

def sourceBody324_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody324_0 sourceBody324_55

def sourceBody324_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 24#64])

def sourceBody324_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 12)

def sourceBody324_59 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 10)

def sourceBody324_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 4) 8

def sourceBody324_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody324_60 sourceBody324_0

def sourceBody324_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody324_59 sourceBody324_61

def sourceBody324_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody324_62 sourceBody324_0

def sourceBody324_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody324_58 sourceBody324_63

def sourceBody324_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody324_0 sourceBody324_64

def sourceBody324_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody324_57 sourceBody324_65

def sourceBody324_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody324_0 sourceBody324_66

def sourceBody324_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody324_56 sourceBody324_67

def sourceBody324_69 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 12)

def sourceBody324_70 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [4]

def sourceBody324_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody324_70 sourceBody324_0

def sourceBody324_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody324_69 sourceBody324_71

def sourceBody324_73 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody324_68 sourceBody324_72

def sourceBody324_74 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody324_44 sourceBody324_73

def sourceBody324_75 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody324_0 sourceBody324_74

def sourceBody324_76 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody324_0 sourceBody324_75

def sourceBody324_77 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody324_39 sourceBody324_76

def sourceBody324_78 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody324_1 sourceBody324_77

def sourceBody324_79 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody324_0 sourceBody324_78

def source324 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (324, 2, sourceBody324_79)
end InitECandidate.Proofs.WordStages
