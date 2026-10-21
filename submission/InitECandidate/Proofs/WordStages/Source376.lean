import InitECandidate.Proofs.WordStages.Source360
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody376_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody376_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody376_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody376_0, 376, 2)) (some 69) ([]) (some (8, sourceBody376_1, 376, 3))

def sourceBody376_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody376_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody376_2 sourceBody376_3

def sourceBody376_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody376_4 sourceBody376_0

def sourceBody376_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 32#64)

def sourceBody376_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody376_8 : WordLangProgHOL (BitVec 64) :=
.call (some (([8]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit
      (Flapjack.Spt.ls PUnit.unit))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody376_0, 376, 4)) (some 68) ([12]) (some (12, sourceBody376_7, 376, 5))

def sourceBody376_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody376_8 sourceBody376_3

def sourceBody376_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody376_9 sourceBody376_0

def sourceBody376_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody376_6 sourceBody376_10

def sourceBody376_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 1#64])

def sourceBody376_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.const 64#64)

def sourceBody376_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 8)

def sourceBody376_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody376_16 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln)
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody376_0, 376, 6)) (some 158) ([10, 16, 6]) (some (10, sourceBody376_15, 376, 7))

def sourceBody376_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody376_16 sourceBody376_3

def sourceBody376_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody376_17 sourceBody376_0

def sourceBody376_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody376_14 sourceBody376_18

def sourceBody376_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody376_13 sourceBody376_19

def sourceBody376_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody376_12 sourceBody376_20

def sourceBody376_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody376_0 sourceBody376_21

def sourceBody376_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody376_0 sourceBody376_22

def sourceBody376_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 4)

def sourceBody376_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 8, Flapjack.WordLangExpHOL.const 12#64])

def sourceBody376_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 20#64)

def sourceBody376_27 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody376_0, 376, 8)) (some 77) ([10, 16, 6]) (some (10, sourceBody376_15, 376, 9))

def sourceBody376_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody376_27 sourceBody376_3

def sourceBody376_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody376_28 sourceBody376_0

def sourceBody376_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody376_26 sourceBody376_29

def sourceBody376_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody376_25 sourceBody376_30

def sourceBody376_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody376_24 sourceBody376_31

def sourceBody376_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody376_0 sourceBody376_32

def sourceBody376_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody376_0 sourceBody376_33

def sourceBody376_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody376_23 sourceBody376_34

def sourceBody376_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 14)

def sourceBody376_37 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody376_0, 376, 10)) (some 70) ([10]) (some (10, sourceBody376_15, 376, 11))

def sourceBody376_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody376_37 sourceBody376_3

def sourceBody376_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody376_38 sourceBody376_0

def sourceBody376_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody376_36 sourceBody376_39

def sourceBody376_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody376_0 sourceBody376_40

def sourceBody376_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody376_0 sourceBody376_41

def sourceBody376_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody376_35 sourceBody376_42

def sourceBody376_44 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody376_45 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [12]

def sourceBody376_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody376_45 sourceBody376_0

def sourceBody376_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody376_44 sourceBody376_46

def sourceBody376_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody376_43 sourceBody376_47

def sourceBody376_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody376_11 sourceBody376_48

def sourceBody376_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody376_0 sourceBody376_49

def sourceBody376_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody376_0 sourceBody376_50

def sourceBody376_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody376_5 sourceBody376_51

def sourceBody376_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody376_0 sourceBody376_52

def sourceBody376_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody376_0 sourceBody376_53

def source376 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (376, 3, sourceBody376_54)
end InitECandidate.Proofs.WordStages
