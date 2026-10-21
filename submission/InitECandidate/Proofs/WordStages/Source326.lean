import InitECandidate.Proofs.WordStages.Source310
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody326_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody326_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add
      [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 24#64]))

def sourceBody326_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 8)

def sourceBody326_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody326_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody326_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody326_6 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 6 (Flapjack.WordRegImm.reg 14) sourceBody326_4 sourceBody326_5

def sourceBody326_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody326_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody326_6 sourceBody326_7

def sourceBody326_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 6)

def sourceBody326_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 8)

def sourceBody326_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [16]

def sourceBody326_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody326_11 sourceBody326_0

def sourceBody326_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody326_10 sourceBody326_12

def sourceBody326_14 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.imm 0#64) sourceBody326_13 sourceBody326_0

def sourceBody326_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody326_14 sourceBody326_7

def sourceBody326_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody326_15 sourceBody326_0

def sourceBody326_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody326_9 sourceBody326_16

def sourceBody326_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody326_8 sourceBody326_17

def sourceBody326_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody326_3 sourceBody326_18

def sourceBody326_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody326_2 sourceBody326_19

def sourceBody326_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 2)

def sourceBody326_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody326_23 : WordLangProgHOL (BitVec 64) :=
.call (some (([16, 6]), ((Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln, Flapjack.Spt.ln)), sourceBody326_0, 326, 2)) (some 321) ([14]) (some (14, sourceBody326_22, 326, 3))

def sourceBody326_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody326_23 sourceBody326_7

def sourceBody326_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody326_24 sourceBody326_0

def sourceBody326_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody326_21 sourceBody326_25

def sourceBody326_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody326_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody326_29 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody326_0, 326, 4)) (some 68) ([10]) (some (10, sourceBody326_28, 326, 5))

def sourceBody326_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody326_29 sourceBody326_7

def sourceBody326_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody326_30 sourceBody326_0

def sourceBody326_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody326_27 sourceBody326_31

def sourceBody326_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 16)

def sourceBody326_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 6)

def sourceBody326_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 14)

def sourceBody326_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody326_37 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody326_0, 326, 6)) (some 158) ([18, 4, 12]) (some (18, sourceBody326_36, 326, 7))

def sourceBody326_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody326_37 sourceBody326_7

def sourceBody326_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody326_38 sourceBody326_0

def sourceBody326_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody326_35 sourceBody326_39

def sourceBody326_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody326_34 sourceBody326_40

def sourceBody326_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody326_33 sourceBody326_41

def sourceBody326_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody326_0 sourceBody326_42

def sourceBody326_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody326_0 sourceBody326_43

def sourceBody326_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 24#64])

def sourceBody326_46 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 14)

def sourceBody326_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.var 18)

def sourceBody326_48 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 10) 4

def sourceBody326_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody326_48 sourceBody326_0

def sourceBody326_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody326_47 sourceBody326_49

def sourceBody326_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody326_50 sourceBody326_0

def sourceBody326_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody326_46 sourceBody326_51

def sourceBody326_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody326_0 sourceBody326_52

def sourceBody326_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody326_45 sourceBody326_53

def sourceBody326_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody326_0 sourceBody326_54

def sourceBody326_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody326_44 sourceBody326_55

def sourceBody326_57 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 14)

def sourceBody326_58 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [10]

def sourceBody326_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody326_58 sourceBody326_0

def sourceBody326_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody326_57 sourceBody326_59

def sourceBody326_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody326_56 sourceBody326_60

def sourceBody326_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody326_32 sourceBody326_61

def sourceBody326_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody326_0 sourceBody326_62

def sourceBody326_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody326_0 sourceBody326_63

def sourceBody326_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody326_26 sourceBody326_64

def sourceBody326_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody326_0 sourceBody326_65

def sourceBody326_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody326_0 sourceBody326_66

def sourceBody326_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody326_0 sourceBody326_67

def sourceBody326_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody326_0 sourceBody326_68

def sourceBody326_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody326_20 sourceBody326_69

def sourceBody326_71 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody326_1 sourceBody326_70

def sourceBody326_72 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody326_0 sourceBody326_71

def source326 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (326, 2, sourceBody326_72)
end InitECandidate.Proofs.WordStages
