import InitECandidate.Proofs.WordStages.Source706
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody722_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody722_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 14)

def sourceBody722_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 12)

def sourceBody722_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody722_4 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody722_0, 722, 2)) (some 89) ([20, 18]) (some (20, sourceBody722_3, 722, 3))

def sourceBody722_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody722_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody722_4 sourceBody722_5

def sourceBody722_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody722_6 sourceBody722_0

def sourceBody722_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody722_2 sourceBody722_7

def sourceBody722_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody722_1 sourceBody722_8

def sourceBody722_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody722_0 sourceBody722_9

def sourceBody722_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody722_0 sourceBody722_10

def sourceBody722_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 8#64])

def sourceBody722_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 10)

def sourceBody722_14 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody722_0, 722, 4)) (some 89) ([20, 18]) (some (20, sourceBody722_3, 722, 5))

def sourceBody722_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody722_14 sourceBody722_5

def sourceBody722_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody722_15 sourceBody722_0

def sourceBody722_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody722_13 sourceBody722_16

def sourceBody722_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody722_12 sourceBody722_17

def sourceBody722_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody722_0 sourceBody722_18

def sourceBody722_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody722_0 sourceBody722_19

def sourceBody722_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody722_11 sourceBody722_20

def sourceBody722_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 16#64])

def sourceBody722_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 8)

def sourceBody722_24 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit
      (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody722_0, 722, 6)) (some 89) ([20, 18]) (some (20, sourceBody722_3, 722, 7))

def sourceBody722_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody722_24 sourceBody722_5

def sourceBody722_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody722_25 sourceBody722_0

def sourceBody722_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody722_23 sourceBody722_26

def sourceBody722_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody722_22 sourceBody722_27

def sourceBody722_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody722_0 sourceBody722_28

def sourceBody722_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody722_0 sourceBody722_29

def sourceBody722_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody722_21 sourceBody722_30

def sourceBody722_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 24#64])

def sourceBody722_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 6)

def sourceBody722_34 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
      (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody722_0, 722, 8)) (some 89) ([20, 18]) (some (20, sourceBody722_3, 722, 9))

def sourceBody722_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody722_34 sourceBody722_5

def sourceBody722_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody722_35 sourceBody722_0

def sourceBody722_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody722_33 sourceBody722_36

def sourceBody722_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody722_32 sourceBody722_37

def sourceBody722_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody722_0 sourceBody722_38

def sourceBody722_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody722_0 sourceBody722_39

def sourceBody722_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody722_31 sourceBody722_40

def sourceBody722_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 32#64])

def sourceBody722_43 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 4)

def sourceBody722_44 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody722_0, 722, 10)) (some 89) ([20, 18]) (some (20, sourceBody722_3, 722, 11))

def sourceBody722_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody722_44 sourceBody722_5

def sourceBody722_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody722_45 sourceBody722_0

def sourceBody722_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody722_43 sourceBody722_46

def sourceBody722_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody722_42 sourceBody722_47

def sourceBody722_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody722_0 sourceBody722_48

def sourceBody722_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody722_0 sourceBody722_49

def sourceBody722_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody722_41 sourceBody722_50

def sourceBody722_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 14, Flapjack.WordLangExpHOL.const 40#64])

def sourceBody722_53 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 2)

def sourceBody722_54 : WordLangProgHOL (BitVec 64) :=
.call (some (([16]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody722_0, 722, 12)) (some 89) ([20, 18]) (some (20, sourceBody722_3, 722, 13))

def sourceBody722_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody722_54 sourceBody722_5

def sourceBody722_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody722_55 sourceBody722_0

def sourceBody722_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody722_53 sourceBody722_56

def sourceBody722_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody722_52 sourceBody722_57

def sourceBody722_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody722_0 sourceBody722_58

def sourceBody722_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody722_0 sourceBody722_59

def sourceBody722_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody722_51 sourceBody722_60

def sourceBody722_62 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody722_63 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [16]

def sourceBody722_64 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody722_63 sourceBody722_0

def sourceBody722_65 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody722_62 sourceBody722_64

def sourceBody722_66 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody722_61 sourceBody722_65

def source722 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (722, 8, sourceBody722_66)
end InitECandidate.Proofs.WordStages
