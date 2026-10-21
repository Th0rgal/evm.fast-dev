import InitECandidate.Proofs.WordStages.Source502
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody518_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody518_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody518_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([6, 16, 4, 14]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody518_0, 518, 2)) (some 471) ([]) (some (10, sourceBody518_1, 518, 3))

def sourceBody518_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody518_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody518_2 sourceBody518_3

def sourceBody518_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody518_4 sourceBody518_0

def sourceBody518_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 5#64)

def sourceBody518_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody518_8 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln)
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit))))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody518_0, 518, 4)) (some 466) ([18]) (some (18, sourceBody518_7, 518, 5))

def sourceBody518_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody518_8 sourceBody518_3

def sourceBody518_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody518_9 sourceBody518_0

def sourceBody518_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody518_6 sourceBody518_10

def sourceBody518_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody518_0 sourceBody518_11

def sourceBody518_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody518_0 sourceBody518_12

def sourceBody518_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 6)

def sourceBody518_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.var 16)

def sourceBody518_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 4)

def sourceBody518_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 14)

def sourceBody518_18 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody518_0, 518, 6)) (some 138) ([18, 2, 12, 8]) (some (18, sourceBody518_7, 518, 7))

def sourceBody518_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody518_18 sourceBody518_3

def sourceBody518_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody518_19 sourceBody518_0

def sourceBody518_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody518_17 sourceBody518_20

def sourceBody518_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody518_16 sourceBody518_21

def sourceBody518_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody518_15 sourceBody518_22

def sourceBody518_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody518_14 sourceBody518_23

def sourceBody518_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2
  (Flapjack.WordLangExpHOL.op Flapjack.BinOp.sub [Flapjack.WordLangExpHOL.const 256#64, Flapjack.WordLangExpHOL.var 10])

def sourceBody518_26 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 2

def sourceBody518_27 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody518_0, 518, 8)) (some 473) ([2]) (some (2, sourceBody518_26, 518, 9))

def sourceBody518_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody518_27 sourceBody518_3

def sourceBody518_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody518_28 sourceBody518_0

def sourceBody518_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody518_25 sourceBody518_29

def sourceBody518_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody518_0 sourceBody518_30

def sourceBody518_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody518_0 sourceBody518_31

def sourceBody518_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 2 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody518_34 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody518_0, 518, 10)) (some 486) ([2]) (some (2, sourceBody518_26, 518, 11))

def sourceBody518_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody518_34 sourceBody518_3

def sourceBody518_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody518_35 sourceBody518_0

def sourceBody518_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody518_33 sourceBody518_36

def sourceBody518_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody518_0 sourceBody518_37

def sourceBody518_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody518_0 sourceBody518_38

def sourceBody518_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody518_32 sourceBody518_39

def sourceBody518_41 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody518_42 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [18]

def sourceBody518_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody518_42 sourceBody518_0

def sourceBody518_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody518_41 sourceBody518_43

def sourceBody518_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody518_40 sourceBody518_44

def sourceBody518_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody518_24 sourceBody518_45

def sourceBody518_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody518_0 sourceBody518_46

def sourceBody518_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody518_0 sourceBody518_47

def sourceBody518_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody518_13 sourceBody518_48

def sourceBody518_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody518_5 sourceBody518_49

def sourceBody518_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody518_0 sourceBody518_50

def sourceBody518_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody518_0 sourceBody518_51

def sourceBody518_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody518_0 sourceBody518_52

def sourceBody518_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody518_0 sourceBody518_53

def sourceBody518_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody518_0 sourceBody518_54

def sourceBody518_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody518_0 sourceBody518_55

def sourceBody518_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody518_0 sourceBody518_56

def sourceBody518_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody518_0 sourceBody518_57

def source518 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (518, 1, sourceBody518_58)
end InitECandidate.Proofs.WordStages
