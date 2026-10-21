import InitECandidate.Proofs.WordStages.Source284
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody300_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody300_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody300_2 : WordLangProgHOL (BitVec 64) :=
.call (some (([10]), ((Flapjack.Spt.bs (Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit
    Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody300_0, 300, 2)) (some 75) ([]) (some (18, sourceBody300_1, 300, 3))

def sourceBody300_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody300_4 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody300_2 sourceBody300_3

def sourceBody300_5 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody300_4 sourceBody300_0

def sourceBody300_6 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 2)

def sourceBody300_7 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 4)

def sourceBody300_8 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 16 (Flapjack.WordLangExpHOL.var 6)

def sourceBody300_9 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 10)

def sourceBody300_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 20

def sourceBody300_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.lookup (Flapjack.WordStore.temp 0#5))

def sourceBody300_12 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody300_11 sourceBody300_0

def sourceBody300_13 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody300_12 sourceBody300_0

def sourceBody300_14 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 10)

def sourceBody300_15 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody300_16 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)))
      Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody300_0, 300, 5)) (some 76) ([8]) (some (8, sourceBody300_15, 300, 6))

def sourceBody300_17 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody300_16 sourceBody300_3

def sourceBody300_18 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody300_17 sourceBody300_0

def sourceBody300_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody300_14 sourceBody300_18

def sourceBody300_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody300_0 sourceBody300_19

def sourceBody300_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody300_0 sourceBody300_20

def sourceBody300_22 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 18)

def sourceBody300_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.set (Flapjack.WordStore.temp 0#5) (Flapjack.WordLangExpHOL.var 20)

def sourceBody300_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody300_23 sourceBody300_0

def sourceBody300_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody300_24 sourceBody300_0

def sourceBody300_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody300_22 sourceBody300_25

def sourceBody300_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody300_0 sourceBody300_26

def sourceBody300_28 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody300_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody300_28 sourceBody300_10

def sourceBody300_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody300_27 sourceBody300_29

def sourceBody300_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody300_21 sourceBody300_30

def sourceBody300_32 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody300_13 sourceBody300_31

def sourceBody300_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody300_3 sourceBody300_32

def sourceBody300_34 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 20 (Flapjack.WordRegImm.imm 1#64) sourceBody300_10 sourceBody300_33

def sourceBody300_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody300_34 sourceBody300_3

def sourceBody300_36 : WordLangProgHOL (BitVec 64) :=
.call (some (([14]), ((Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody300_0, 300, 4)) (some 299) ([20, 8, 16, 12]) (some (20, sourceBody300_35, 300, 7))

def sourceBody300_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody300_36 sourceBody300_3

def sourceBody300_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody300_37 sourceBody300_0

def sourceBody300_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody300_9 sourceBody300_38

def sourceBody300_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody300_8 sourceBody300_39

def sourceBody300_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody300_7 sourceBody300_40

def sourceBody300_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody300_6 sourceBody300_41

def sourceBody300_43 : WordLangProgHOL (BitVec 64) :=
.call (some (([20]), ((Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody300_0, 300, 8)) (some 76) ([8]) (some (8, sourceBody300_15, 300, 9))

def sourceBody300_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody300_43 sourceBody300_3

def sourceBody300_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody300_44 sourceBody300_0

def sourceBody300_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody300_14 sourceBody300_45

def sourceBody300_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody300_0 sourceBody300_46

def sourceBody300_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody300_0 sourceBody300_47

def sourceBody300_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody300_42 sourceBody300_48

def sourceBody300_50 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 20 (Flapjack.WordLangExpHOL.var 14)

def sourceBody300_51 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [20]

def sourceBody300_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody300_51 sourceBody300_0

def sourceBody300_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody300_50 sourceBody300_52

def sourceBody300_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody300_49 sourceBody300_53

def sourceBody300_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody300_0 sourceBody300_54

def sourceBody300_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody300_0 sourceBody300_55

def sourceBody300_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody300_0 sourceBody300_56

def sourceBody300_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody300_0 sourceBody300_57

def sourceBody300_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody300_5 sourceBody300_58

def sourceBody300_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody300_0 sourceBody300_59

def sourceBody300_61 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody300_0 sourceBody300_60

def source300 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (300, 4, sourceBody300_61)
end InitECandidate.Proofs.WordStages
