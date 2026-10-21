import InitECandidate.Proofs.WordStages.Source361
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody377_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody377_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 2)

def sourceBody377_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody377_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([18, 8]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody377_0, 377, 2)) (some 373) ([16]) (some (16, sourceBody377_2, 377, 3))

def sourceBody377_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody377_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody377_3 sourceBody377_4

def sourceBody377_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody377_5 sourceBody377_0

def sourceBody377_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody377_1 sourceBody377_6

def sourceBody377_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody377_9 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody377_0, 377, 4)) (some 69) ([]) (some (12, sourceBody377_8, 377, 5))

def sourceBody377_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody377_9 sourceBody377_4

def sourceBody377_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody377_10 sourceBody377_0

def sourceBody377_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 72#64)

def sourceBody377_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody377_14 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody377_0, 377, 6)) (some 68) ([20]) (some (20, sourceBody377_13, 377, 7))

def sourceBody377_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody377_14 sourceBody377_4

def sourceBody377_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody377_15 sourceBody377_0

def sourceBody377_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody377_12 sourceBody377_16

def sourceBody377_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 12)

def sourceBody377_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 4#64)

def sourceBody377_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.inst
  (Flapjack.WordLangInst.mem Flapjack.WordMemOp.store8 6 (Flapjack.WordLangAddr.addr 20 0#64))

def sourceBody377_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody377_20 sourceBody377_0

def sourceBody377_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody377_19 sourceBody377_21

def sourceBody377_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody377_18 sourceBody377_22

def sourceBody377_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 2)

def sourceBody377_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 8)

def sourceBody377_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 12, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody377_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody377_28 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody377_0, 377, 8)) (some 375) ([6, 14, 10]) (some (6, sourceBody377_27, 377, 9))

def sourceBody377_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody377_28 sourceBody377_4

def sourceBody377_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody377_29 sourceBody377_0

def sourceBody377_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody377_26 sourceBody377_30

def sourceBody377_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody377_25 sourceBody377_31

def sourceBody377_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody377_24 sourceBody377_32

def sourceBody377_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody377_0 sourceBody377_33

def sourceBody377_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody377_0 sourceBody377_34

def sourceBody377_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody377_23 sourceBody377_35

def sourceBody377_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 12)

def sourceBody377_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 4)

def sourceBody377_39 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn Flapjack.Spt.ln
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody377_0, 377, 10)) (some 376) ([6, 14]) (some (6, sourceBody377_27, 377, 11))

def sourceBody377_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody377_39 sourceBody377_4

def sourceBody377_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody377_40 sourceBody377_0

def sourceBody377_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody377_38 sourceBody377_41

def sourceBody377_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody377_37 sourceBody377_42

def sourceBody377_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody377_0 sourceBody377_43

def sourceBody377_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody377_0 sourceBody377_44

def sourceBody377_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody377_36 sourceBody377_45

def sourceBody377_47 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 16)

def sourceBody377_48 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody377_0, 377, 12)) (some 70) ([6]) (some (6, sourceBody377_27, 377, 13))

def sourceBody377_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody377_48 sourceBody377_4

def sourceBody377_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody377_49 sourceBody377_0

def sourceBody377_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody377_47 sourceBody377_50

def sourceBody377_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody377_0 sourceBody377_51

def sourceBody377_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody377_0 sourceBody377_52

def sourceBody377_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody377_46 sourceBody377_53

def sourceBody377_55 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody377_56 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [20]

def sourceBody377_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody377_56 sourceBody377_0

def sourceBody377_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody377_55 sourceBody377_57

def sourceBody377_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody377_54 sourceBody377_58

def sourceBody377_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody377_17 sourceBody377_59

def sourceBody377_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody377_0 sourceBody377_60

def sourceBody377_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody377_0 sourceBody377_61

def sourceBody377_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody377_11 sourceBody377_62

def sourceBody377_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody377_0 sourceBody377_63

def sourceBody377_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody377_0 sourceBody377_64

def sourceBody377_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody377_7 sourceBody377_65

def sourceBody377_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody377_0 sourceBody377_66

def sourceBody377_68 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody377_0 sourceBody377_67

def sourceBody377_69 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody377_0 sourceBody377_68

def sourceBody377_70 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody377_0 sourceBody377_69

def source377 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (377, 3, sourceBody377_70)
end InitECandidate.Proofs.WordStages
