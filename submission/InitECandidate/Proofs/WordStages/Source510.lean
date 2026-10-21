import InitECandidate.Proofs.WordStages.Source494
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody510_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody510_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody510_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([8, 22, 4, 18]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody510_0, 510, 2)) (some 471) ([]) (some (12, sourceBody510_1, 510, 3))

def sourceBody510_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody510_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody510_2 sourceBody510_3

def sourceBody510_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody510_4 sourceBody510_0

def sourceBody510_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody510_7 : WordLangProgHOL (BitVec 64) :=
.call (some (([12, 26, 2, 16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody510_0, 510, 4)) (some 471) ([]) (some (10, sourceBody510_6, 510, 5))

def sourceBody510_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody510_7 sourceBody510_3

def sourceBody510_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody510_8 sourceBody510_0

def sourceBody510_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 3#64)

def sourceBody510_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 24

def sourceBody510_12 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody510_0, 510, 6)) (some 466) ([24]) (some (24, sourceBody510_11, 510, 7))

def sourceBody510_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody510_12 sourceBody510_3

def sourceBody510_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody510_13 sourceBody510_0

def sourceBody510_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody510_10 sourceBody510_14

def sourceBody510_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody510_0 sourceBody510_15

def sourceBody510_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody510_0 sourceBody510_16

def sourceBody510_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.var 12])

def sourceBody510_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and [Flapjack.WordLangExpHOL.var 22, Flapjack.WordLangExpHOL.var 26])

def sourceBody510_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.var 2])

def sourceBody510_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.and [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.var 16])

def sourceBody510_22 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody510_0, 510, 8)) (some 472) ([24, 6, 20, 14]) (some (24, sourceBody510_11, 510, 9))

def sourceBody510_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody510_22 sourceBody510_3

def sourceBody510_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody510_23 sourceBody510_0

def sourceBody510_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody510_21 sourceBody510_24

def sourceBody510_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody510_20 sourceBody510_25

def sourceBody510_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody510_19 sourceBody510_26

def sourceBody510_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody510_18 sourceBody510_27

def sourceBody510_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody510_0 sourceBody510_28

def sourceBody510_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody510_0 sourceBody510_29

def sourceBody510_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody510_17 sourceBody510_30

def sourceBody510_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody510_33 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody510_0, 510, 10)) (some 486) ([24]) (some (24, sourceBody510_11, 510, 11))

def sourceBody510_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody510_33 sourceBody510_3

def sourceBody510_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody510_34 sourceBody510_0

def sourceBody510_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody510_32 sourceBody510_35

def sourceBody510_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody510_0 sourceBody510_36

def sourceBody510_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody510_0 sourceBody510_37

def sourceBody510_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody510_31 sourceBody510_38

def sourceBody510_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody510_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [10]

def sourceBody510_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody510_41 sourceBody510_0

def sourceBody510_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody510_40 sourceBody510_42

def sourceBody510_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody510_39 sourceBody510_43

def sourceBody510_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody510_9 sourceBody510_44

def sourceBody510_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody510_0 sourceBody510_45

def sourceBody510_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody510_0 sourceBody510_46

def sourceBody510_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody510_0 sourceBody510_47

def sourceBody510_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody510_0 sourceBody510_48

def sourceBody510_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody510_0 sourceBody510_49

def sourceBody510_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody510_0 sourceBody510_50

def sourceBody510_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody510_0 sourceBody510_51

def sourceBody510_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody510_0 sourceBody510_52

def sourceBody510_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody510_5 sourceBody510_53

def sourceBody510_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody510_0 sourceBody510_54

def sourceBody510_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody510_0 sourceBody510_55

def sourceBody510_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody510_0 sourceBody510_56

def sourceBody510_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody510_0 sourceBody510_57

def sourceBody510_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody510_0 sourceBody510_58

def sourceBody510_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody510_0 sourceBody510_59

def sourceBody510_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody510_0 sourceBody510_60

def sourceBody510_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody510_0 sourceBody510_61

def source510 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (510, 1, sourceBody510_62)
end InitECandidate.Proofs.WordStages
