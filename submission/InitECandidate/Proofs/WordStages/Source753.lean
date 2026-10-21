import InitECandidate.Proofs.WordStages.Source737
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody753_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody753_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody753_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln, Flapjack.Spt.ln)), sourceBody753_0, 753, 2)) (some 69) ([]) (some (12, sourceBody753_1, 753, 3))

def sourceBody753_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody753_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody753_2 sourceBody753_3

def sourceBody753_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody753_4 sourceBody753_0

def sourceBody753_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 4 (Flapjack.WordLangExpHOL.const 576#64)

def sourceBody753_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 4

def sourceBody753_8 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody753_0, 753, 4)) (some 68) ([4]) (some (4, sourceBody753_7, 753, 5))

def sourceBody753_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody753_8 sourceBody753_3

def sourceBody753_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody753_9 sourceBody753_0

def sourceBody753_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody753_6 sourceBody753_10

def sourceBody753_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 12)

def sourceBody753_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody753_14 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody753_0, 753, 6)) (some 752) ([10]) (some (10, sourceBody753_13, 753, 7))

def sourceBody753_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody753_14 sourceBody753_3

def sourceBody753_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody753_15 sourceBody753_0

def sourceBody753_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody753_12 sourceBody753_16

def sourceBody753_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody753_0 sourceBody753_17

def sourceBody753_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody753_0 sourceBody753_18

def sourceBody753_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 2)

def sourceBody753_21 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 12)

def sourceBody753_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.const 576#64)

def sourceBody753_23 : WordLangProgHOL (BitVec 64) :=
.call (some (([4]), ((Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody753_0, 753, 8)) (some 79) ([10, 8, 14]) (some (10, sourceBody753_13, 753, 9))

def sourceBody753_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody753_23 sourceBody753_3

def sourceBody753_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody753_24 sourceBody753_0

def sourceBody753_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody753_22 sourceBody753_25

def sourceBody753_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody753_21 sourceBody753_26

def sourceBody753_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody753_20 sourceBody753_27

def sourceBody753_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 6)

def sourceBody753_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody753_31 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody753_0, 753, 10)) (some 70) ([8]) (some (8, sourceBody753_30, 753, 11))

def sourceBody753_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody753_31 sourceBody753_3

def sourceBody753_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody753_32 sourceBody753_0

def sourceBody753_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody753_29 sourceBody753_33

def sourceBody753_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody753_0 sourceBody753_34

def sourceBody753_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody753_0 sourceBody753_35

def sourceBody753_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 4)

def sourceBody753_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [10]

def sourceBody753_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody753_38 sourceBody753_0

def sourceBody753_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody753_37 sourceBody753_39

def sourceBody753_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody753_36 sourceBody753_40

def sourceBody753_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody753_28 sourceBody753_41

def sourceBody753_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody753_0 sourceBody753_42

def sourceBody753_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody753_0 sourceBody753_43

def sourceBody753_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody753_19 sourceBody753_44

def sourceBody753_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody753_11 sourceBody753_45

def sourceBody753_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody753_0 sourceBody753_46

def sourceBody753_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody753_0 sourceBody753_47

def sourceBody753_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody753_5 sourceBody753_48

def sourceBody753_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody753_0 sourceBody753_49

def sourceBody753_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody753_0 sourceBody753_50

def source753 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (753, 2, sourceBody753_51)
end InitECandidate.Proofs.WordStages
