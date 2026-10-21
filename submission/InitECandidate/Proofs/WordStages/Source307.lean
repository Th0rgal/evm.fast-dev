import InitECandidate.Proofs.WordStages.Source291
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody307_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody307_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody307_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody307_0, 307, 2)) (some 69) ([]) (some (20, sourceBody307_1, 307, 3))

def sourceBody307_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody307_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody307_2 sourceBody307_3

def sourceBody307_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody307_4 sourceBody307_0

def sourceBody307_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 24 (Flapjack.WordLangExpHOL.var 2)

def sourceBody307_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 4)

def sourceBody307_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 6)

def sourceBody307_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 24

def sourceBody307_10 : WordLangProgHOL (BitVec 64) :=
.call (some (([20, 16]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody307_0, 307, 4)) (some 306) ([24, 8, 18]) (some (24, sourceBody307_9, 307, 5))

def sourceBody307_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody307_10 sourceBody307_3

def sourceBody307_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody307_11 sourceBody307_0

def sourceBody307_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody307_8 sourceBody307_12

def sourceBody307_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody307_7 sourceBody307_13

def sourceBody307_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody307_6 sourceBody307_14

def sourceBody307_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14
  (Flapjack.WordLangExpHOL.load
    (Flapjack.WordLangExpHOL.op Flapjack.BinOp.add [Flapjack.WordLangExpHOL.var 2, Flapjack.WordLangExpHOL.const 0#64]))

def sourceBody307_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 20)

def sourceBody307_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 16)

def sourceBody307_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody307_20 : WordLangProgHOL (BitVec 64) :=
.call (some (([24, 8, 18]), ((Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody307_0, 307, 6)) (some 302) ([14, 22, 12]) (some (14, sourceBody307_19, 307, 7))

def sourceBody307_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody307_20 sourceBody307_3

def sourceBody307_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody307_21 sourceBody307_0

def sourceBody307_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody307_18 sourceBody307_22

def sourceBody307_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody307_17 sourceBody307_23

def sourceBody307_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody307_16 sourceBody307_24

def sourceBody307_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 10)

def sourceBody307_27 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 22

def sourceBody307_28 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody307_0, 307, 8)) (some 70) ([22]) (some (22, sourceBody307_27, 307, 9))

def sourceBody307_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody307_28 sourceBody307_3

def sourceBody307_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody307_29 sourceBody307_0

def sourceBody307_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody307_26 sourceBody307_30

def sourceBody307_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody307_0 sourceBody307_31

def sourceBody307_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody307_0 sourceBody307_32

def sourceBody307_34 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 24)

def sourceBody307_35 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 22 (Flapjack.WordLangExpHOL.var 8)

def sourceBody307_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 18)

def sourceBody307_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [14, 22, 12]

def sourceBody307_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody307_37 sourceBody307_0

def sourceBody307_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody307_36 sourceBody307_38

def sourceBody307_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody307_35 sourceBody307_39

def sourceBody307_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody307_34 sourceBody307_40

def sourceBody307_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody307_33 sourceBody307_41

def sourceBody307_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody307_25 sourceBody307_42

def sourceBody307_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody307_0 sourceBody307_43

def sourceBody307_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody307_0 sourceBody307_44

def sourceBody307_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody307_0 sourceBody307_45

def sourceBody307_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody307_0 sourceBody307_46

def sourceBody307_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody307_0 sourceBody307_47

def sourceBody307_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody307_0 sourceBody307_48

def sourceBody307_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody307_15 sourceBody307_49

def sourceBody307_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody307_0 sourceBody307_50

def sourceBody307_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody307_0 sourceBody307_51

def sourceBody307_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody307_0 sourceBody307_52

def sourceBody307_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody307_0 sourceBody307_53

def sourceBody307_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody307_5 sourceBody307_54

def sourceBody307_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody307_0 sourceBody307_55

def sourceBody307_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody307_0 sourceBody307_56

def source307 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (307, 4, sourceBody307_57)
end InitECandidate.Proofs.WordStages
