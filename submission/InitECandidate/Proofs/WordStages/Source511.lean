import InitECandidate.Proofs.WordStages.Source495
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody511_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody511_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody511_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([8, 22, 4, 18]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody511_0, 511, 2)) (some 471) ([]) (some (12, sourceBody511_1, 511, 3))

def sourceBody511_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody511_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody511_2 sourceBody511_3

def sourceBody511_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody511_4 sourceBody511_0

def sourceBody511_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody511_7 : WordLangProgHOL (BitVec 64) :=
.call (some (([12, 26, 2, 16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody511_0, 511, 4)) (some 471) ([]) (some (10, sourceBody511_6, 511, 5))

def sourceBody511_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody511_7 sourceBody511_3

def sourceBody511_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody511_8 sourceBody511_0

def sourceBody511_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 3#64)

def sourceBody511_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 24

def sourceBody511_12 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs
      (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))
        (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) (Flapjack.Spt.ls PUnit.unit)))
      PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
        (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody511_0, 511, 6)) (some 466) ([24]) (some (24, sourceBody511_11, 511, 7))

def sourceBody511_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody511_12 sourceBody511_3

def sourceBody511_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody511_13 sourceBody511_0

def sourceBody511_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody511_10 sourceBody511_14

def sourceBody511_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody511_0 sourceBody511_15

def sourceBody511_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody511_0 sourceBody511_16

def sourceBody511_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.or [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.var 12])

def sourceBody511_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.or [Flapjack.WordLangExpHOL.var 22, Flapjack.WordLangExpHOL.var 26])

def sourceBody511_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.or [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.var 2])

def sourceBody511_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.or [Flapjack.WordLangExpHOL.var 18, Flapjack.WordLangExpHOL.var 16])

def sourceBody511_22 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody511_0, 511, 8)) (some 472) ([24, 6, 20, 14]) (some (24, sourceBody511_11, 511, 9))

def sourceBody511_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody511_22 sourceBody511_3

def sourceBody511_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody511_23 sourceBody511_0

def sourceBody511_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody511_21 sourceBody511_24

def sourceBody511_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody511_20 sourceBody511_25

def sourceBody511_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody511_19 sourceBody511_26

def sourceBody511_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody511_18 sourceBody511_27

def sourceBody511_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody511_0 sourceBody511_28

def sourceBody511_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody511_0 sourceBody511_29

def sourceBody511_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody511_17 sourceBody511_30

def sourceBody511_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody511_33 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody511_0, 511, 10)) (some 486) ([24]) (some (24, sourceBody511_11, 511, 11))

def sourceBody511_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody511_33 sourceBody511_3

def sourceBody511_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody511_34 sourceBody511_0

def sourceBody511_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody511_32 sourceBody511_35

def sourceBody511_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody511_0 sourceBody511_36

def sourceBody511_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody511_0 sourceBody511_37

def sourceBody511_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody511_31 sourceBody511_38

def sourceBody511_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody511_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [10]

def sourceBody511_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody511_41 sourceBody511_0

def sourceBody511_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody511_40 sourceBody511_42

def sourceBody511_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody511_39 sourceBody511_43

def sourceBody511_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody511_9 sourceBody511_44

def sourceBody511_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody511_0 sourceBody511_45

def sourceBody511_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody511_0 sourceBody511_46

def sourceBody511_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody511_0 sourceBody511_47

def sourceBody511_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody511_0 sourceBody511_48

def sourceBody511_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody511_0 sourceBody511_49

def sourceBody511_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody511_0 sourceBody511_50

def sourceBody511_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody511_0 sourceBody511_51

def sourceBody511_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody511_0 sourceBody511_52

def sourceBody511_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody511_5 sourceBody511_53

def sourceBody511_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody511_0 sourceBody511_54

def sourceBody511_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody511_0 sourceBody511_55

def sourceBody511_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody511_0 sourceBody511_56

def sourceBody511_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody511_0 sourceBody511_57

def sourceBody511_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody511_0 sourceBody511_58

def sourceBody511_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody511_0 sourceBody511_59

def sourceBody511_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody511_0 sourceBody511_60

def sourceBody511_62 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody511_0 sourceBody511_61

def source511 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (511, 1, sourceBody511_62)
end InitECandidate.Proofs.WordStages
