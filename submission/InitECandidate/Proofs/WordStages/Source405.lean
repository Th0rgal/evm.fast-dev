import InitECandidate.Proofs.WordStages.Source389
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody405_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody405_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 2)

def sourceBody405_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 4)

def sourceBody405_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody405_4 : WordLangProgHOL (BitVec 64) :=
.call (some (([10, 16]), ((Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody405_0, 405, 2)) (some 186) ([12, 18]) (some (12, sourceBody405_3, 405, 3))

def sourceBody405_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody405_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody405_4 sourceBody405_5

def sourceBody405_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody405_6 sourceBody405_0

def sourceBody405_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody405_2 sourceBody405_7

def sourceBody405_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody405_1 sourceBody405_8

def sourceBody405_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 10)

def sourceBody405_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody405_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody405_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody405_14 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.equal) 18 (Flapjack.WordRegImm.reg 8) sourceBody405_12 sourceBody405_13

def sourceBody405_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody405_14 sourceBody405_5

def sourceBody405_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 18)

def sourceBody405_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody405_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [12, 18]

def sourceBody405_19 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody405_18 sourceBody405_0

def sourceBody405_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody405_13 sourceBody405_19

def sourceBody405_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody405_17 sourceBody405_20

def sourceBody405_22 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.WordRegImm.imm 0#64) sourceBody405_21 sourceBody405_0

def sourceBody405_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody405_22 sourceBody405_5

def sourceBody405_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody405_23 sourceBody405_0

def sourceBody405_25 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody405_16 sourceBody405_24

def sourceBody405_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody405_15 sourceBody405_25

def sourceBody405_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody405_11 sourceBody405_26

def sourceBody405_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody405_10 sourceBody405_27

def sourceBody405_29 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 16)

def sourceBody405_30 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 6)

def sourceBody405_31 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 8

def sourceBody405_32 : WordLangProgHOL (BitVec 64) :=
.call (some (([12, 18]), ((Flapjack.Spt.ls PUnit.unit, Flapjack.Spt.ln)), sourceBody405_0, 405, 4)) (some 186) ([8, 14]) (some (8, sourceBody405_31, 405, 5))

def sourceBody405_33 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody405_32 sourceBody405_5

def sourceBody405_34 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody405_33 sourceBody405_0

def sourceBody405_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody405_30 sourceBody405_34

def sourceBody405_36 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody405_29 sourceBody405_35

def sourceBody405_37 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 12)

def sourceBody405_38 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [8, 14]

def sourceBody405_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody405_38 sourceBody405_0

def sourceBody405_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody405_16 sourceBody405_39

def sourceBody405_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody405_37 sourceBody405_40

def sourceBody405_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody405_36 sourceBody405_41

def sourceBody405_43 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody405_0 sourceBody405_42

def sourceBody405_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody405_0 sourceBody405_43

def sourceBody405_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody405_0 sourceBody405_44

def sourceBody405_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody405_0 sourceBody405_45

def sourceBody405_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody405_28 sourceBody405_46

def sourceBody405_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody405_9 sourceBody405_47

def sourceBody405_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody405_0 sourceBody405_48

def sourceBody405_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody405_0 sourceBody405_49

def sourceBody405_51 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody405_0 sourceBody405_50

def sourceBody405_52 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody405_0 sourceBody405_51

def source405 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (405, 4, sourceBody405_52)
end InitECandidate.Proofs.WordStages
