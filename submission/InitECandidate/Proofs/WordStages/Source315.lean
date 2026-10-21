import InitECandidate.Proofs.WordStages.Source299
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody315_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody315_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 14

def sourceBody315_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([18]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit
      (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)))
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody315_0, 315, 2)) (some 75) ([]) (some (14, sourceBody315_1, 315, 3))

def sourceBody315_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody315_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody315_2 sourceBody315_3

def sourceBody315_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody315_4 sourceBody315_0

def sourceBody315_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 2)

def sourceBody315_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 4)

def sourceBody315_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 6)

def sourceBody315_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 8)

def sourceBody315_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody315_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.lookup (Flapjack.WordStore.temp 0#5))

def sourceBody315_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody315_11 sourceBody315_0

def sourceBody315_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody315_12 sourceBody315_0

def sourceBody315_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 18)

def sourceBody315_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 16

def sourceBody315_16 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody315_0, 315, 5)) (some 76) ([16]) (some (16, sourceBody315_15, 315, 6))

def sourceBody315_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody315_16 sourceBody315_3

def sourceBody315_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody315_17 sourceBody315_0

def sourceBody315_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody315_14 sourceBody315_18

def sourceBody315_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody315_0 sourceBody315_19

def sourceBody315_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody315_0 sourceBody315_20

def sourceBody315_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 14)

def sourceBody315_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 10)

def sourceBody315_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody315_23 sourceBody315_0

def sourceBody315_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody315_24 sourceBody315_0

def sourceBody315_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody315_22 sourceBody315_25

def sourceBody315_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody315_0 sourceBody315_26

def sourceBody315_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 5#64)

def sourceBody315_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody315_28 sourceBody315_10

def sourceBody315_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody315_27 sourceBody315_29

def sourceBody315_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody315_21 sourceBody315_30

def sourceBody315_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody315_13 sourceBody315_31

def sourceBody315_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody315_3 sourceBody315_32

def sourceBody315_34 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.imm 5#64) sourceBody315_10 sourceBody315_33

def sourceBody315_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody315_34 sourceBody315_3

def sourceBody315_36 : WordLangProgHOL (BitVec 64) :=
.call (some (([22]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody315_0, 315, 4)) (some 314) ([10, 16, 12, 20]) (some (10, sourceBody315_35, 315, 7))

def sourceBody315_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody315_36 sourceBody315_3

def sourceBody315_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody315_37 sourceBody315_0

def sourceBody315_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody315_9 sourceBody315_38

def sourceBody315_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody315_8 sourceBody315_39

def sourceBody315_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody315_7 sourceBody315_40

def sourceBody315_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody315_6 sourceBody315_41

def sourceBody315_43 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody315_0, 315, 8)) (some 76) ([16]) (some (16, sourceBody315_15, 315, 9))

def sourceBody315_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody315_43 sourceBody315_3

def sourceBody315_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody315_44 sourceBody315_0

def sourceBody315_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody315_14 sourceBody315_45

def sourceBody315_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody315_0 sourceBody315_46

def sourceBody315_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody315_0 sourceBody315_47

def sourceBody315_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody315_42 sourceBody315_48

def sourceBody315_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 22)

def sourceBody315_51 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [10]

def sourceBody315_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody315_51 sourceBody315_0

def sourceBody315_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody315_50 sourceBody315_52

def sourceBody315_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody315_49 sourceBody315_53

def sourceBody315_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody315_0 sourceBody315_54

def sourceBody315_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody315_0 sourceBody315_55

def sourceBody315_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody315_0 sourceBody315_56

def sourceBody315_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody315_0 sourceBody315_57

def sourceBody315_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody315_5 sourceBody315_58

def sourceBody315_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody315_0 sourceBody315_59

def sourceBody315_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody315_0 sourceBody315_60

def source315 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (315, 5, sourceBody315_61)
end InitECandidate.Proofs.WordStages
