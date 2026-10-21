import InitECandidate.Proofs.WordStages.Source409
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody425_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody425_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 2)

def sourceBody425_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 24

def sourceBody425_3 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody425_0, 425, 2)) (some 403) ([24]) (some (24, sourceBody425_2, 425, 3))

def sourceBody425_4 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody425_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody425_3 sourceBody425_4

def sourceBody425_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody425_5 sourceBody425_0

def sourceBody425_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody425_1 sourceBody425_6

def sourceBody425_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 18)

def sourceBody425_9 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody425_0, 425, 4)) (some 391) ([24]) (some (24, sourceBody425_2, 425, 5))

def sourceBody425_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody425_9 sourceBody425_4

def sourceBody425_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody425_10 sourceBody425_0

def sourceBody425_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody425_8 sourceBody425_11

def sourceBody425_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.const 8#64])

def sourceBody425_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 4)

def sourceBody425_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 6)

def sourceBody425_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 8)

def sourceBody425_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 10)

def sourceBody425_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 12)

def sourceBody425_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store (Flapjack.WordLangExpHOL.var 24) 14

def sourceBody425_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody425_19 sourceBody425_0

def sourceBody425_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody425_18 sourceBody425_20

def sourceBody425_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 20)

def sourceBody425_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 24, Flapjack.WordLangExpHOL.const 8#64])
  14

def sourceBody425_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody425_23 sourceBody425_0

def sourceBody425_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody425_22 sourceBody425_24

def sourceBody425_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 16)

def sourceBody425_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 24, Flapjack.WordLangExpHOL.const 16#64])
  14

def sourceBody425_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody425_27 sourceBody425_0

def sourceBody425_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody425_26 sourceBody425_28

def sourceBody425_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 22)

def sourceBody425_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.store
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 24, Flapjack.WordLangExpHOL.const 24#64])
  14

def sourceBody425_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody425_31 sourceBody425_0

def sourceBody425_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody425_30 sourceBody425_32

def sourceBody425_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody425_33 sourceBody425_0

def sourceBody425_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody425_29 sourceBody425_34

def sourceBody425_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody425_25 sourceBody425_35

def sourceBody425_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody425_21 sourceBody425_36

def sourceBody425_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody425_17 sourceBody425_37

def sourceBody425_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody425_0 sourceBody425_38

def sourceBody425_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody425_16 sourceBody425_39

def sourceBody425_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody425_0 sourceBody425_40

def sourceBody425_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody425_15 sourceBody425_41

def sourceBody425_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody425_0 sourceBody425_42

def sourceBody425_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody425_14 sourceBody425_43

def sourceBody425_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody425_0 sourceBody425_44

def sourceBody425_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody425_13 sourceBody425_45

def sourceBody425_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody425_0 sourceBody425_46

def sourceBody425_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody425_12 sourceBody425_47

def sourceBody425_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 2)

def sourceBody425_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 18)

def sourceBody425_51 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody425_52 : WordLangProgHOL (BitVec 64) :=
.call (some (([24]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody425_0, 425, 6)) (some 419) ([12, 20]) (some (12, sourceBody425_51, 425, 7))

def sourceBody425_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody425_52 sourceBody425_4

def sourceBody425_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody425_53 sourceBody425_0

def sourceBody425_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody425_50 sourceBody425_54

def sourceBody425_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody425_49 sourceBody425_55

def sourceBody425_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody425_0 sourceBody425_56

def sourceBody425_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody425_0 sourceBody425_57

def sourceBody425_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody425_48 sourceBody425_58

def sourceBody425_60 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody425_61 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [24]

def sourceBody425_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody425_61 sourceBody425_0

def sourceBody425_63 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody425_60 sourceBody425_62

def sourceBody425_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody425_59 sourceBody425_63

def sourceBody425_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody425_7 sourceBody425_64

def sourceBody425_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody425_0 sourceBody425_65

def sourceBody425_67 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody425_0 sourceBody425_66

def source425 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (425, 6, sourceBody425_67)
end InitECandidate.Proofs.WordStages
