import InitECandidate.Proofs.WordStages.Source232
import Flapjack.Pancake.WordLang
set_option maxRecDepth 1000000
set_option maxHeartbeats 0
open Flapjack
namespace InitECandidate.Proofs.WordStages
def sourceBody248_0 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.skip

def sourceBody248_1 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 2)

def sourceBody248_2 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 4)

def sourceBody248_3 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 12

def sourceBody248_4 : WordLangProgHOL (BitVec 64) :=
.call (some (([10, 16]), ((Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.ls PUnit.unit) Flapjack.Spt.ln) PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody248_0, 248, 2)) (some 94) ([12, 18]) (some (12, sourceBody248_3, 248, 3))

def sourceBody248_5 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.tick

def sourceBody248_6 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody248_4 sourceBody248_5

def sourceBody248_7 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody248_6 sourceBody248_0

def sourceBody248_8 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody248_2 sourceBody248_7

def sourceBody248_9 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody248_1 sourceBody248_8

def sourceBody248_10 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 16)

def sourceBody248_11 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody248_12 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 1#64)

def sourceBody248_13 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 0#64)

def sourceBody248_14 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 18 (Flapjack.WordRegImm.reg 8) sourceBody248_12 sourceBody248_13

def sourceBody248_15 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody248_14 sourceBody248_5

def sourceBody248_16 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 14 (Flapjack.WordLangExpHOL.var 18)

def sourceBody248_17 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 30#64)

def sourceBody248_18 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.raise 18

def sourceBody248_19 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs
    (Flapjack.Spt.bn (Flapjack.Spt.bs Flapjack.Spt.ln PUnit.unit (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody248_0, 248, 4)) (some 245) ([18]) (some (18, sourceBody248_18, 248, 5))

def sourceBody248_20 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody248_19 sourceBody248_5

def sourceBody248_21 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody248_20 sourceBody248_0

def sourceBody248_22 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody248_17 sourceBody248_21

def sourceBody248_23 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody248_0 sourceBody248_22

def sourceBody248_24 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody248_0 sourceBody248_23

def sourceBody248_25 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.WordRegImm.imm 0#64) sourceBody248_24 sourceBody248_0

def sourceBody248_26 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody248_25 sourceBody248_5

def sourceBody248_27 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody248_26 sourceBody248_0

def sourceBody248_28 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody248_16 sourceBody248_27

def sourceBody248_29 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody248_15 sourceBody248_28

def sourceBody248_30 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody248_11 sourceBody248_29

def sourceBody248_31 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody248_10 sourceBody248_30

def sourceBody248_32 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.var 6)

def sourceBody248_33 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 8 (Flapjack.WordLangExpHOL.var 10)

def sourceBody248_34 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.lower) 18 (Flapjack.WordRegImm.reg 8) sourceBody248_12 sourceBody248_13

def sourceBody248_35 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody248_34 sourceBody248_5

def sourceBody248_36 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 18 (Flapjack.WordLangExpHOL.const 31#64)

def sourceBody248_37 : WordLangProgHOL (BitVec 64) :=
.call (some (([12]), ((Flapjack.Spt.bs (Flapjack.Spt.bn (Flapjack.Spt.bn Flapjack.Spt.ln (Flapjack.Spt.ls PUnit.unit)) Flapjack.Spt.ln)
    PUnit.unit Flapjack.Spt.ln,
  Flapjack.Spt.ln)), sourceBody248_0, 248, 6)) (some 245) ([18]) (some (18, sourceBody248_18, 248, 7))

def sourceBody248_38 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody248_37 sourceBody248_5

def sourceBody248_39 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody248_38 sourceBody248_0

def sourceBody248_40 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody248_36 sourceBody248_39

def sourceBody248_41 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody248_0 sourceBody248_40

def sourceBody248_42 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody248_0 sourceBody248_41

def sourceBody248_43 : WordLangProgHOL (BitVec 64) :=
.ite (Flapjack.Cmp.notEqual) 14 (Flapjack.WordRegImm.imm 0#64) sourceBody248_42 sourceBody248_0

def sourceBody248_44 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody248_43 sourceBody248_5

def sourceBody248_45 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody248_44 sourceBody248_0

def sourceBody248_46 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody248_16 sourceBody248_45

def sourceBody248_47 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody248_35 sourceBody248_46

def sourceBody248_48 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody248_33 sourceBody248_47

def sourceBody248_49 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody248_32 sourceBody248_48

def sourceBody248_50 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody248_31 sourceBody248_49

def sourceBody248_51 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.assign 12 (Flapjack.WordLangExpHOL.var 10)

def sourceBody248_52 : WordLangProgHOL (BitVec 64) :=
Flapjack.WordLangProgHOL.return 0 [12]

def sourceBody248_53 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody248_52 sourceBody248_0

def sourceBody248_54 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody248_51 sourceBody248_53

def sourceBody248_55 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody248_50 sourceBody248_54

def sourceBody248_56 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody248_9 sourceBody248_55

def sourceBody248_57 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody248_0 sourceBody248_56

def sourceBody248_58 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody248_0 sourceBody248_57

def sourceBody248_59 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody248_0 sourceBody248_58

def sourceBody248_60 : WordLangProgHOL (BitVec 64) :=
.seq sourceBody248_0 sourceBody248_59

def source248 : Nat × Nat × Flapjack.WordLangProgHOL (BitVec 64) :=
  (248, 4, sourceBody248_60)
end InitECandidate.Proofs.WordStages
