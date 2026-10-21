import InitECandidate.Proofs.WordStages.Source756
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody772_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody772_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody772_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody772_0, 772, 2)) (some 69) ([]) (some (6, sourceBody772_1, 772, 3))

def sourceBody772_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody772_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody772_2 sourceBody772_3

def sourceBody772_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody772_4 sourceBody772_0

def sourceBody772_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 96#64)

def sourceBody772_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody772_8 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody772_0, 772, 4)) (some 68) ([10]) (some (10, sourceBody772_7, 772, 5))

def sourceBody772_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody772_8 sourceBody772_3

def sourceBody772_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody772_9 sourceBody772_0

def sourceBody772_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody772_6 sourceBody772_10

def sourceBody772_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 6)

def sourceBody772_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 2)

def sourceBody772_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody772_15 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody772_0, 772, 6)) (some 769) ([8, 14]) (some (8, sourceBody772_14, 772, 7))

def sourceBody772_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody772_15 sourceBody772_3

def sourceBody772_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody772_16 sourceBody772_0

def sourceBody772_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody772_13 sourceBody772_17

def sourceBody772_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody772_12 sourceBody772_18

def sourceBody772_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody772_0 sourceBody772_19

def sourceBody772_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody772_0 sourceBody772_20

def sourceBody772_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 4)

def sourceBody772_23 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit)
      (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody772_0, 772, 8)) (some 724) ([8, 14]) (some (8, sourceBody772_14, 772, 9))

def sourceBody772_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody772_23 sourceBody772_3

def sourceBody772_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody772_24 sourceBody772_0

def sourceBody772_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody772_22 sourceBody772_25

def sourceBody772_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody772_12 sourceBody772_26

def sourceBody772_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody772_0 sourceBody772_27

def sourceBody772_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody772_0 sourceBody772_28

def sourceBody772_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody772_21 sourceBody772_29

def sourceBody772_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 6, Flapjack.WordLangExpHOL.const 48#64])

def sourceBody772_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 4, Flapjack.WordLangExpHOL.const 64#64])

def sourceBody772_33 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody772_0, 772, 10)) (some 724) ([8, 14]) (some (8, sourceBody772_14, 772, 11))

def sourceBody772_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody772_33 sourceBody772_3

def sourceBody772_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody772_34 sourceBody772_0

def sourceBody772_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody772_32 sourceBody772_35

def sourceBody772_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody772_31 sourceBody772_36

def sourceBody772_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody772_0 sourceBody772_37

def sourceBody772_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody772_0 sourceBody772_38

def sourceBody772_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody772_30 sourceBody772_39

def sourceBody772_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 12)

def sourceBody772_42 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody772_0, 772, 12)) (some 70) ([8]) (some (8, sourceBody772_14, 772, 13))

def sourceBody772_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody772_42 sourceBody772_3

def sourceBody772_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody772_43 sourceBody772_0

def sourceBody772_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody772_41 sourceBody772_44

def sourceBody772_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody772_0 sourceBody772_45

def sourceBody772_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody772_0 sourceBody772_46

def sourceBody772_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody772_40 sourceBody772_47

def sourceBody772_49 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody772_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [10]

def sourceBody772_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody772_50 sourceBody772_0

def sourceBody772_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody772_49 sourceBody772_51

def sourceBody772_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody772_48 sourceBody772_52

def sourceBody772_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody772_11 sourceBody772_53

def sourceBody772_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody772_0 sourceBody772_54

def sourceBody772_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody772_0 sourceBody772_55

def sourceBody772_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody772_5 sourceBody772_56

def sourceBody772_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody772_0 sourceBody772_57

def sourceBody772_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody772_0 sourceBody772_58

def source772 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (772, 3, sourceBody772_59)
end InitECandidate.Proofs.WordStages
