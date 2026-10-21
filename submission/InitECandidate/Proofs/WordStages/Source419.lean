import InitECandidate.Proofs.WordStages.Source403
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody419_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody419_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 2)

def sourceBody419_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 4)

def sourceBody419_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 6

def sourceBody419_4 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody419_0, 419, 2)) (some 415) ([6, 10]) (some (6, sourceBody419_3, 419, 3))

def sourceBody419_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody419_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody419_4 sourceBody419_5

def sourceBody419_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody419_6 sourceBody419_0

def sourceBody419_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody419_2 sourceBody419_7

def sourceBody419_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody419_1 sourceBody419_8

def sourceBody419_10 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody419_0 sourceBody419_9

def sourceBody419_11 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody419_0 sourceBody419_10

def sourceBody419_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.var 4)

def sourceBody419_13 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs (Flapjack.Spt.ls PUnit.unit) PUnit.unit Flapjack.Spt.ln, Flapjack.Spt.ln)), sourceBody419_0, 419, 4)) (some 412) ([6]) (some (6, sourceBody419_3, 419, 5))

def sourceBody419_14 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody419_13 sourceBody419_5

def sourceBody419_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody419_14 sourceBody419_0

def sourceBody419_16 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody419_12 sourceBody419_15

def sourceBody419_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 12)

def sourceBody419_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody419_19 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody419_20 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody419_21 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 10 (Flapjack.WordRegImm.reg 8) sourceBody419_19 sourceBody419_20

def sourceBody419_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody419_21 sourceBody419_5

def sourceBody419_23 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 10)

def sourceBody419_24 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 10 (Flapjack.WordLangExpHOL.var 2)

def sourceBody419_25 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 10

def sourceBody419_26 : WordLangProgHOL (BitVec 64) :=
.call (some (([6]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody419_0, 419, 6)) (some 418) ([10]) (some (10, sourceBody419_25, 419, 7))

def sourceBody419_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody419_26 sourceBody419_5

def sourceBody419_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody419_27 sourceBody419_0

def sourceBody419_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody419_24 sourceBody419_28

def sourceBody419_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody419_0 sourceBody419_29

def sourceBody419_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody419_0 sourceBody419_30

def sourceBody419_32 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.WordRegImm.imm 0#64) sourceBody419_31 sourceBody419_0

def sourceBody419_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody419_32 sourceBody419_5

def sourceBody419_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody419_33 sourceBody419_0

def sourceBody419_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody419_23 sourceBody419_34

def sourceBody419_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody419_22 sourceBody419_35

def sourceBody419_37 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody419_18 sourceBody419_36

def sourceBody419_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody419_17 sourceBody419_37

def sourceBody419_39 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 6 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody419_40 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [6]

def sourceBody419_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody419_40 sourceBody419_0

def sourceBody419_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody419_39 sourceBody419_41

def sourceBody419_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody419_38 sourceBody419_42

def sourceBody419_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody419_16 sourceBody419_43

def sourceBody419_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody419_0 sourceBody419_44

def sourceBody419_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody419_0 sourceBody419_45

def sourceBody419_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody419_11 sourceBody419_46

def source419 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (419, 3, sourceBody419_47)
end InitECandidate.Proofs.WordStages
